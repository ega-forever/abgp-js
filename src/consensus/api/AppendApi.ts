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

const ec = new EC('secp256k1');

export default class AppendApi {
  private abgp: ABGP;

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
    const stateHash = AppendApi.hashData(`${key}:${value}:${version}${1}`);

    if (await this.abgp.storage.has(hash)) {
      return;
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.getByTimestamp(timestamp)).length;

    const signature = buildPartialSignature(
      this.abgp.privateKey,
      hash
    );

    const record: RecordModel = RecordModel.fromPlainObject({
      hash,
      stateHash,
      key,
      value,
      version,
      signaturesMap: {
        [this.abgp.publicKey]: signature
      },
      timestamp,
      timestampIndex,
      signatureType: SignatureType.INTERMEDIATE,
      publicKeys: [this.abgp.publicKey]
    });

    await this.saveItem(record);
    this.abgp.emit(EventTypes.STATE_UPDATE);
    return hash;
  }

  public async remoteAppend(remoteRecord: RecordModel, peerNode: NodeModel, peerNodeRoot: string) {
    const hash = AppendApi.hashData(`${remoteRecord.key}:${remoteRecord.value}:${remoteRecord.version}`);

    if (hash !== remoteRecord.hash) {
      return null;
    }

    if (remoteRecord.timestamp < peerNode.lastUpdateTimestamp
      || (remoteRecord.timestamp === peerNode.lastUpdateTimestamp && remoteRecord.timestampIndex < peerNode.lastUpdateTimestampIndex)
    ) {
      return null;
    }

    const sortedPublicKeys = [...this.abgp.publicKeys.keys()].sort();
    const involvedPublicKeys: string[] = remoteRecord.publicKeyMap.toString(2)
      .padStart(this.abgp.publicKeys.size, '0')
      .split('')
      .reduce((arr, elem, index) => {
        if (elem === '0') {
          return arr;
        }

        const publicKey = sortedPublicKeys[index];
        arr.push(publicKey);

        return arr;
      }, []);

    if (remoteRecord.signatureType === SignatureType.INTERMEDIATE) {
      for (const publicKey of remoteRecord.signaturesMap.keys()) {
        const signature = remoteRecord.signaturesMap.get(publicKey);
        const isValid = partialSignatureVerify(signature, publicKey, hash);
        if (!isValid) {
          return null;
        }
      }
    } else {
      const calcMultiPublicKey = buildSharedPublicKeyX(involvedPublicKeys, hash);
      const multiPublicKey = [...remoteRecord.signaturesMap.keys()][0];

      if (calcMultiPublicKey !== multiPublicKey) {
        return null;
      }

      const multisig = remoteRecord.signaturesMap.get(multiPublicKey);
      const isValid = verify(multisig, multiPublicKey);
      if (!isValid) {
        return null;
      }
    }

    const timestamp = Date.now();
    const timestampIndex = (await this.abgp.storage.getByTimestamp(timestamp)).length;

    /** object is mutated here, so no need to save it to map * */
    let localRecord: RecordModel = await this.abgp.storage.get(hash);

    if (localRecord && localRecord.signatureType === SignatureType.MULTISIG && remoteRecord.signatureType === SignatureType.INTERMEDIATE) {
      return null;
    }

    if (localRecord && localRecord.signatureType === SignatureType.MULTISIG && remoteRecord.signatureType === SignatureType.MULTISIG) {
      const localMultiSigPublicKey = [...localRecord.signaturesMap.keys()][0];
      const remoteMultiSigPublicKey = [...remoteRecord.signaturesMap.keys()][0];

      if (localMultiSigPublicKey === remoteMultiSigPublicKey || localMultiSigPublicKey > remoteMultiSigPublicKey) {
        this.updatePeerNodeLastState(peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
        return null;
      }

      const remoteMultiSig = remoteRecord.signaturesMap.get(remoteMultiSigPublicKey);

      localRecord.signaturesMap = new Map<string, string>();
      localRecord.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
      localRecord.publicKeys = new Set<string>(involvedPublicKeys);
      localRecord.stateHash = remoteRecord.stateHash;
      localRecord.timestamp = timestamp;
      localRecord.timestampIndex = timestampIndex;

      await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
      this.abgp.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    if (remoteRecord.signatureType === SignatureType.MULTISIG) {
      const remoteMultiSigPublicKey = [...remoteRecord.signaturesMap.keys()][0];
      const remoteMultiSig = remoteRecord.signaturesMap.get(remoteMultiSigPublicKey);

      if (!localRecord) {
        localRecord = RecordModel.fromPlainObject({
          hash: remoteRecord.hash,
          stateHash: remoteRecord.stateHash,
          timestamp,
          timestampIndex,
          key: remoteRecord.key,
          value: remoteRecord.value,
          version: remoteRecord.version,
          signaturesMap: Object.fromEntries(remoteRecord.signaturesMap),
          signatureType: SignatureType.MULTISIG,
          publicKeys: involvedPublicKeys
        });
      } else {
        localRecord.stateHash = remoteRecord.stateHash;
        localRecord.timestamp = timestamp;
        localRecord.timestampIndex = timestampIndex;
        localRecord.signaturesMap = new Map<string, string>();
        localRecord.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
        localRecord.publicKeys = new Set<string>(involvedPublicKeys);
        localRecord.signatureType = SignatureType.MULTISIG;
      }

      await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
      this.abgp.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    if (!localRecord) {
      localRecord = RecordModel.fromPlainObject({
        hash: remoteRecord.hash,
        stateHash: remoteRecord.stateHash,
        timestamp,
        timestampIndex,
        key: remoteRecord.key,
        value: remoteRecord.value,
        version: remoteRecord.version,
        signaturesMap: Object.fromEntries(remoteRecord.signaturesMap),
        signatureType: SignatureType.INTERMEDIATE,
        publicKeys: involvedPublicKeys
      });

      const signature = buildPartialSignature(
        this.abgp.privateKey,
        hash
      );

      localRecord.signaturesMap.set(this.abgp.publicKey, signature);
      localRecord.publicKeys.add(this.abgp.publicKey);
      localRecord.stateHash = AppendApi.hashData(`${localRecord.hash}:${localRecord.value}:${localRecord.version}${localRecord.publicKeys.size}`);
    } else {
      for (const publicKey of remoteRecord.signaturesMap.keys()) {
        const signature = remoteRecord.signaturesMap.get(publicKey);
        localRecord.signaturesMap.set(publicKey, signature);
        localRecord.publicKeys.add(publicKey);
      }

      localRecord.timestamp = timestamp;
      localRecord.timestampIndex = timestampIndex;
      localRecord.stateHash = AppendApi.hashData(`${localRecord.hash}:${localRecord.value}:${localRecord.version}${localRecord.publicKeys.size}`);
    }

    if (localRecord.signaturesMap.size >= this.abgp.majority()) {
      const publicKeysForMusig = [...localRecord.signaturesMap.keys()].sort().slice(0, this.abgp.majority());
      const totalPublicKeys = localRecord.publicKeys.size;
      const signaturesForMusig = publicKeysForMusig.map((publicKey) => localRecord.signaturesMap.get(publicKey));
      const multiPublicKey = buildSharedPublicKeyX(publicKeysForMusig, hash);

      const multiSignature = buildSharedSignature(signaturesForMusig);
      localRecord.signaturesMap = new Map<string, string>();
      localRecord.signaturesMap.set(multiPublicKey, multiSignature);
      localRecord.signatureType = SignatureType.MULTISIG;
      localRecord.publicKeys = new Set<string>(publicKeysForMusig);
      localRecord.stateHash = AppendApi.hashData(`${localRecord.hash}:${localRecord.value}:${localRecord.version}${totalPublicKeys + 1}`);
    }

    await this.saveItem(localRecord, peerNode, peerNodeRoot, remoteRecord.timestamp, remoteRecord.timestampIndex);
    this.abgp.emit(EventTypes.STATE_UPDATE);
  }

  private async saveItem(item: RecordModel, peerNode?: NodeModel, peerRoot?: string, peerTimestamp?: number, peerTimestampIndex?: number) {
    const prevItem = await this.abgp.storage.get(item.hash);

    await this.abgp.storage.save(item);
    this.abgp.lastUpdateTimestamp = item.timestamp;
    this.abgp.lastUpdateTimestampIndex = item.timestampIndex;

    if (peerNode) {
      this.updatePeerNodeLastState(peerNode, peerRoot, peerTimestamp, peerTimestampIndex);
    }

    if (
      item.signatureType === SignatureType.MULTISIG &&
      ((prevItem && prevItem.signatureType === SignatureType.INTERMEDIATE) || !prevItem)
    ) {
      this.abgp.stateRoot = new BN(this.abgp.stateRoot, 16).add(new BN(item.stateHash, 16)).mod(ec.n).toString(16);
    }
  }

  private updatePeerNodeLastState(peerNode?: NodeModel, peerRoot?: string, peerTimestamp?: number, peerTimestampIndex?: number) {
    // eslint-disable-next-line no-param-reassign
    peerNode.stateRoot = peerRoot;
    // eslint-disable-next-line no-param-reassign
    peerNode.lastUpdateTimestamp = peerTimestamp;
    // eslint-disable-next-line no-param-reassign
    peerNode.lastUpdateTimestampIndex = peerTimestampIndex;
  }
}
