import crypto from 'crypto';
import BN from 'bn.js';
import { ec as EC } from 'elliptic';
import ABGP from '../main';
import {
  buildPartialSignature,
  buildSharedPublicKeyX,
  buildSharedSignature,
  partialSignatureVerify,
  verify
} from '../utils/cryptoUtils';
import SignatureType from '../constants/SignatureType';
import EventTypes from '../constants/EventTypes';
import NodeModel from '../models/NodeModel';
import RecordModel from '../models/RecordModel';
import { isEqualSet, isSetIncludesAllKeys } from '../utils/utils';
import Semaphore from '../utils/Semaphore';
import Benchmark from '../utils/BenchmarkDecorator';

const ec = new EC('secp256k1');

export default class AppendApi {
  private readonly abgp: ABGP;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
  }

  private static hashData(data: string) {
    return crypto.createHash('sha256')
      .update(data)
      .digest('hex');
  }

  public async append(key: string, value: string, version: number = 1) {
    const hash = AppendApi.hashData(`${key}:${value}:${version}`);

    if (await this.abgp.storage.Record.has(hash)) {
      return;
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.Record.getByTimestamp(timestamp)).length;

    const signature = buildPartialSignature(
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

  @Benchmark
  public async remoteAppend(remoteRecord: RecordModel, peerNode: NodeModel, peerNodeRoot: string) {
    const hash = AppendApi.hashData(`${remoteRecord.key}:${remoteRecord.value}:${remoteRecord.version}`);

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

    if (remoteRecord.signatureType === SignatureType.INTERMEDIATE) {
      for (const publicKey of remoteRecord.signaturesMap.keys()) {
        const signature = remoteRecord.signaturesMap.get(publicKey);
        const isValid = partialSignatureVerify(signature, publicKey, hash);
        if (!isValid) {
          this.abgp.logger.trace(`wrong INTERMEDIATE signature for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
          return null;
        }
      }
    } else {
      const calcMultiPublicKey = buildSharedPublicKeyX(Array.from(remoteRecord.publicKeys), hash);
      const multiPublicKey = [...remoteRecord.signaturesMap.keys()][0];

      if (calcMultiPublicKey !== multiPublicKey) {
        this.abgp.logger.trace(`wrong MULTISIG publickey for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
        return null;
      }

      const multisig = remoteRecord.signaturesMap.get(multiPublicKey);
      const isValid = verify(multisig, multiPublicKey);
      if (!isValid) {
        this.abgp.logger.trace(`wrong MULTISIG signature for record ${remoteRecord.hash} and public key ${peerNode.publicKey}`);
        return null;
      }
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.Record.getByTimestamp(timestamp)).length;

    let localRecord: RecordModel = await this.abgp.storage.Record.get(hash);

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

      const signature = buildPartialSignature(
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
      const multiPublicKey = buildSharedPublicKeyX(publicKeysForMusig, hash);

      const multiSignature = buildSharedSignature(signaturesForMusig);
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
      item.stateHash = new BN(lastState.root, 16).add(new BN(item.hash, 16)).mod(ec.n).toString(16);
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
