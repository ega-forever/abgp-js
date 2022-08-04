import ABGP from '../main';
import SignatureType from '../constants/SignatureType';
import EventTypes from '../constants/EventTypes';
import NodeModel from '../models/NodeModel';
import RecordModel from '../models/RecordModel';
import { isEqualSet, isSetIncludesAllKeys } from '../utils/utils';
import Semaphore from '../utils/Semaphore';

export default class AppendApi {
  private readonly abgp: ABGP;

  private readonly semaphore: Semaphore;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
    this.semaphore = new Semaphore(1);
  }

  public async append(key: string, value: string, version: number = 1) {
    return this.semaphore.callFunction(this.appendUnSafe.bind(this), key, value, version);
  }

  private async appendUnSafe(key: string, value: string, version: number = 1) {
    const hash = this.abgp.crypto.hash(`${key}:${value}:${version}`);

    if (await this.abgp.storage.Record.has(hash)) {
      return;
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.Record.getByTimestamp(timestamp)).length;

    const signature = await this.abgp.crypto.buildPartialSignature(
      this.abgp.privateKey,
      hash
    );

    const record: RecordModel = new RecordModel({
      hash,
      key,
      value,
      version,
      signaturesMap: new Map<string, string>([[this.abgp.publicKey, signature]]),
      timestamp,
      timestampIndex,
      signatureType: SignatureType.INTERMEDIATE,
      publicKeys: new Set<string>([this.abgp.publicKey])
    });

    await this.saveItem(record);
    this.abgp.emit(EventTypes.STATE_UPDATE);
    return hash;
  }

  public async remoteAppend(remoteRecord: RecordModel, peerNode: NodeModel, peerNodeRoot: string) {
    return this.semaphore.callFunction(this.remoteAppendUnsafe.bind(this), remoteRecord, peerNode, peerNodeRoot);
  }

  public async remoteAppendUnsafe(remoteRecord: RecordModel, peerNode: NodeModel, peerNodeRoot: string) {
    const hash = this.abgp.crypto.hash(`${remoteRecord.key}:${remoteRecord.value}:${remoteRecord.version}`);

    if (hash !== remoteRecord.hash) {
      this.abgp.logger.trace(`different hashes for record ${hash} vs ${remoteRecord.hash} on public key ${peerNode.publicKey}`);
      return null;
    }

    const peerNodeState = await peerNode.getState();

    if (remoteRecord.timestamp < peerNodeState.timestamp
      || (remoteRecord.timestamp === peerNodeState.timestamp && remoteRecord.timestampIndex < peerNodeState.timestampIndex)
    ) {
      this.abgp.logger.trace(`supplied outdated remote record with timestamp ${remoteRecord.timestamp} vs ${peerNodeState.timestamp}`);
      return null;
    }

    let localRecord: RecordModel = await this.abgp.storage.Record.get(hash);

    if (remoteRecord.signatureType === SignatureType.INTERMEDIATE) {
      for (const publicKey of remoteRecord.signaturesMap.keys()) {
        const signature = remoteRecord.signaturesMap.get(publicKey);

        let isValid = false;

        if (localRecord && localRecord.publicKeys.has(publicKey)) {
          isValid = localRecord.signaturesMap.get(publicKey) === signature;
        } else if (localRecord && localRecord.signatureType === SignatureType.MULTISIG) {
          isValid = true;
        } else {
          isValid = await this.abgp.crypto.partialSignatureVerify(signature, publicKey, hash);
        }

        if (!isValid) {
          this.abgp.logger.trace(`wrong INTERMEDIATE signature for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
          return null;
        }
      }
    } else {
      const multiPublicKey = [...remoteRecord.signaturesMap.keys()][0];

      let isValid = false;

      if (localRecord && localRecord.signatureType === SignatureType.MULTISIG && [...localRecord.signaturesMap.keys()][0] === multiPublicKey) {
        isValid = remoteRecord.signaturesMap.get(multiPublicKey) === localRecord.signaturesMap.get(multiPublicKey);
      } else {
        const calcMultiPublicKey = await this.abgp.crypto.buildSharedPublicKeyX(Array.from(remoteRecord.publicKeys), hash);

        if (calcMultiPublicKey !== multiPublicKey) {
          this.abgp.logger.trace(`wrong MULTISIG publickey for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
          return null;
        }

        const multisig = remoteRecord.signaturesMap.get(multiPublicKey);
        isValid = await this.abgp.crypto.verify(multisig, multiPublicKey);
      }

      if (!isValid) {
        this.abgp.logger.trace(`wrong MULTISIG signature for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
        return null;
      }
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.Record.getByTimestamp(timestamp)).length;

    if (
      (localRecord && localRecord.signatureType === SignatureType.MULTISIG && remoteRecord.signatureType === SignatureType.INTERMEDIATE) ||
      (localRecord && isSetIncludesAllKeys(remoteRecord.publicKeys, localRecord.publicKeys)) ||
      (localRecord && isEqualSet(localRecord.publicKeys, remoteRecord.publicKeys)
      )
    ) {
      await peerNode.saveState(remoteRecord.timestamp, remoteRecord.timestampIndex, peerNodeRoot);
      this.abgp.logger.trace(`update peer node state (record is not updated with hash ${remoteRecord.hash} and public key ${peerNode.publicKey})`);
      return null;
    }

    if (localRecord && localRecord.signatureType === SignatureType.MULTISIG && remoteRecord.signatureType === SignatureType.MULTISIG) {
      const localMultiSigPublicKey = [...localRecord.signaturesMap.keys()][0];
      const remoteMultiSigPublicKey = [...remoteRecord.signaturesMap.keys()][0];

      if (localMultiSigPublicKey === remoteMultiSigPublicKey || localMultiSigPublicKey > remoteMultiSigPublicKey) {
        await peerNode.saveState(remoteRecord.timestamp, remoteRecord.timestampIndex, peerNodeRoot);
        this.abgp.logger.trace(`update peer node state (MULTISIG record is not updated with hash ${remoteRecord.hash} and public key ${peerNode.publicKey})`);
        return null;
      }

      const remoteMultiSig = remoteRecord.signaturesMap.get(remoteMultiSigPublicKey);

      localRecord.signaturesMap = new Map<string, string>([[remoteMultiSigPublicKey, remoteMultiSig]]);
      localRecord.publicKeys = new Set<string>(remoteRecord.publicKeys);
      localRecord.timestamp = timestamp;
      localRecord.timestampIndex = timestampIndex;

      await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
      this.abgp.emit(EventTypes.STATE_UPDATE);
      this.abgp.logger.trace(`update peer node state and record (higher MULTISIG signatures) for record with hash ${remoteRecord.hash} and public key ${peerNode.publicKey})`);
      return null;
    }

    if (remoteRecord.signatureType === SignatureType.MULTISIG) {
      const remoteMultiSigPublicKey = [...remoteRecord.signaturesMap.keys()][0];
      const remoteMultiSig = remoteRecord.signaturesMap.get(remoteMultiSigPublicKey);

      if (!localRecord) {
        localRecord = new RecordModel({
          hash: remoteRecord.hash,
          timestamp,
          timestampIndex,
          key: remoteRecord.key,
          value: remoteRecord.value,
          version: remoteRecord.version,
          signaturesMap: new Map<string, string>(remoteRecord.signaturesMap),
          signatureType: SignatureType.MULTISIG,
          publicKeys: new Set<string>(remoteRecord.publicKeys)
        });
      } else {
        localRecord.timestamp = timestamp;
        localRecord.timestampIndex = timestampIndex;
        localRecord.signaturesMap = new Map<string, string>([[remoteMultiSigPublicKey, remoteMultiSig]]);
        localRecord.publicKeys = new Set<string>(remoteRecord.publicKeys);
        localRecord.signatureType = SignatureType.MULTISIG;
      }

      await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
      this.abgp.emit(EventTypes.STATE_UPDATE);
      this.abgp.logger.trace(`save MULTISIG record (no local record exist) with hash ${remoteRecord.hash} and public key ${peerNode.publicKey})`);
      return null;
    }

    if (!localRecord) {
      localRecord = remoteRecord.cloneObject();
      localRecord.timestamp = timestamp;
      localRecord.timestampIndex = timestampIndex;
      localRecord.signatureType = SignatureType.INTERMEDIATE;

      const signature = await this.abgp.crypto.buildPartialSignature(
        this.abgp.privateKey,
        hash
      );

      localRecord.signaturesMap.set(this.abgp.publicKey, signature);
      localRecord.publicKeys.add(this.abgp.publicKey);
    } else {
      for (const publicKey of remoteRecord.signaturesMap.keys()) {
        const signature = remoteRecord.signaturesMap.get(publicKey);
        localRecord.signaturesMap.set(publicKey, signature);
        localRecord.publicKeys.add(publicKey);
      }

      localRecord.timestamp = timestamp;
      localRecord.timestampIndex = timestampIndex;
    }

    if (localRecord.signaturesMap.size >= this.abgp.majority()) {
      const publicKeysForMusig = [...localRecord.signaturesMap.keys()].sort().slice(0, this.abgp.majority());
      const signaturesForMusig = publicKeysForMusig.map((publicKey) => localRecord.signaturesMap.get(publicKey));
      const multiPublicKey = await this.abgp.crypto.buildSharedPublicKeyX(publicKeysForMusig, hash);

      const multiSignature = await this.abgp.crypto.buildSharedSignature(signaturesForMusig);
      localRecord.signaturesMap = new Map<string, string>([[multiPublicKey, multiSignature]]);
      localRecord.signatureType = SignatureType.MULTISIG;
      localRecord.publicKeys = new Set<string>(publicKeysForMusig);
    }

    this.abgp.logger.trace(`save record ${localRecord.signatureType === SignatureType.MULTISIG ? 'MULTISIG' : 'INTERMEDIATE'} with hash ${remoteRecord.hash} and public key ${peerNode.publicKey})`);
    await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
    this.abgp.emit(EventTypes.STATE_UPDATE);
  }

  private async saveItem(item: RecordModel, peerNode?: NodeModel, peerRoot?: string, peerTimestamp?: number, peerTimestampIndex?: number) {
    const prevItem = await this.abgp.storage.Record.get(item.hash);
    const lastState = await this.abgp.getState();

    if (lastState.timestamp > item.timestamp) {
      this.abgp.logger.trace(`WARNING! downgrade timestamp ${lastState.timestamp} vs ${item.timestamp}`);
    }

    if (
      item.signatureType === SignatureType.MULTISIG &&
      ((prevItem && prevItem.signatureType === SignatureType.INTERMEDIATE) || !prevItem)
    ) {
      // eslint-disable-next-line no-param-reassign
      item.stateHash = this.abgp.crypto.math.addMod(lastState.root, item.hash);
      await this.abgp.saveState(item.timestamp, item.timestampIndex, item.stateHash);
    } else {
      await this.abgp.saveState(item.timestamp, item.timestampIndex, lastState.root);
    }

    await this.abgp.storage.Record.save(item);

    if (peerNode) {
      await peerNode.saveState(peerTimestamp, peerTimestampIndex, peerRoot);
    }
  }
}
