import crypto from 'crypto';
import { EventEmitter } from 'events';
import BN from 'bn.js';
import { ec as EC } from 'elliptic';
import EventTypes from '../constants/EventTypes';
import SignatureType from '../constants/SignatureType';
import {
  buildPartialSignature,
  buildSharedPublicKeyX,
  buildSharedSignature,
  partialSignatureVerify, verify
} from '../utils/cryptoUtils';

const ec = new EC('secp256k1');

export class DbItem {
  public hash: string;

  public stateHash: string;

  public key: string;

  public value: string;

  public version: number;

  public timestamp: number;

  public timestampIndex: number;

  public signaturesMap: Map<string, string>; // signature to public key

  public signatureType: number;

  public publicKeys?: Set<string>;

  public publicKeyMap?: number;

  public static fromPlainObject(obj: any) {
    const dbItem = new DbItem();

    dbItem.hash = obj.hash;
    dbItem.stateHash = obj.stateHash;
    dbItem.key = obj.key;
    dbItem.value = obj.value;
    dbItem.version = obj.version;
    dbItem.timestamp = obj.timestamp;
    dbItem.timestampIndex = obj.timestampIndex;
    dbItem.signaturesMap = obj.signaturesMap ? new Map(Object.entries(obj.signaturesMap)) : new Map<string, string>();
    dbItem.signatureType = obj.signatureType;
    dbItem.publicKeys = obj.publicKeys ? new Set(obj.publicKeys) : new Set<string>();
    dbItem.publicKeyMap = obj.publicKeyMap;

    return dbItem;
  }

  public toPlainObject(publicKeys?: string[]) {
    const signaturesMapObj = [...this.signaturesMap.keys()]
      .reduce((result, key) => {
        // eslint-disable-next-line no-param-reassign
        result[key] = this.signaturesMap.get(key);
        return result;
      }, {});

    const publicKeysMapDouble = publicKeys ? publicKeys.sort().map((publicKey) => (this.publicKeys.has(publicKey) ? 1 : 0)).join('') : null;

    return {
      hash: this.hash,
      stateHash: this.stateHash,
      key: this.key,
      value: this.value,
      version: this.version,
      timestamp: this.timestamp,
      timestampIndex: this.timestampIndex,
      signaturesMap: signaturesMapObj,
      signatureType: this.signatureType,
      publicKeys: publicKeys ? null : (this.publicKeys ? [...this.publicKeys] : []),
      publicKeyMap: this.publicKeyMap || parseInt(publicKeysMapDouble, 2)
    };
  }

  public cloneObject() {
    const obj = this.toPlainObject();
    return DbItem.fromPlainObject(obj);
  }
}

class NodeModel extends EventEmitter {
  get address(): string {
    return this.nodeAddress;
  }

  public gossipInterval: {
    min: number,
    max: number
  };

  public batchReplicationSize: number;

  public sendSignalToRandomPeer: boolean;

  public readonly privateKey: string;

  public readonly publicKey: string;

  public stateRoot: string;

  public lastUpdateTimestamp: number;

  public lastUpdateTimestampIndex: number;

  // eslint-disable-next-line no-use-before-define
  public readonly nodes: Map<string, NodeModel> = new Map<string, NodeModel>();

  public readonly db: Map<string, DbItem>;

  private readonly nodeAddress: string;

  public readonly publicKeys: Set<string>;

  public constructor(
    privateKey: string,
    multiaddr: string
  ) {
    super();
    this.privateKey = privateKey;
    this.publicKey = multiaddr.match(/\w+$/).toString();
    this.nodeAddress = multiaddr.split(/\w+$/)[0].replace(/\/$/, '');
    this.db = new Map<string, DbItem>();
    this.lastUpdateTimestamp = 0;
    this.lastUpdateTimestampIndex = 0;
    this.stateRoot = '0';
    this.publicKeys = new Set<string>();
  }

  public hashData(data: string) {
    return crypto.createHash('sha256')
      .update(data)
      .digest('hex');
  }

  public majority() { // todo majority should be set in config, and node links should be checked by majority
    return Math.floor(this.publicKeys.size / 2) + 1;
  }

  private getDbItem(hash: string) {
    const item = this.db.get(hash);

    if (!item) {
      return null;
    }

    return item.cloneObject();
  }

  private setDbItem(dbItem: DbItem) {
    this.db.set(dbItem.hash, dbItem);
  }

  public getStateRoot() {
    return this.stateRoot;
  }

  public append(key: string, value: string, version: number = 1) {
    const hash = this.hashData(`${key}:${value}:${version}`);
    const stateHash = this.hashData(`${key}:${value}:${version}${1}`);

    if (this.db.has(hash)) {
      return;
    }

    const timestamp = Date.now();
    const timestampIndex = [...this.db.values()].filter((v) => v.timestamp === timestamp).length;

    const signature = buildPartialSignature(
      this.privateKey,
      hash
    );

    const dbItem: DbItem = DbItem.fromPlainObject({
      hash,
      stateHash,
      key,
      value,
      version,
      signaturesMap: {
        [this.publicKey]: signature
      },
      timestamp,
      timestampIndex,
      signatureType: SignatureType.INTERMEDIATE,
      publicKeys: [this.publicKey]
    });

    this.saveItem(dbItem);
    this.emit(EventTypes.STATE_UPDATE);
    return hash;
  }

  public remoteAppend(remoteItem: DbItem, peerNode: NodeModel) {
    const hash = this.hashData(`${remoteItem.key}:${remoteItem.value}:${remoteItem.version}`);

    if (hash !== remoteItem.hash) {
      return null;
    }

    if (remoteItem.timestamp < peerNode.lastUpdateTimestamp
      || (remoteItem.timestamp === peerNode.lastUpdateTimestamp && remoteItem.timestampIndex < peerNode.lastUpdateTimestampIndex)
    ) {
      return null;
    }

    const sortedPublicKeys = [...this.publicKeys.keys()].sort();
    const involvedPublicKeys: string[] = remoteItem.publicKeyMap.toString(2)
      .padStart(this.publicKeys.size, '0')
      .split('')
      .reduce((arr, elem, index) => {
        if (elem === '0') {
          return arr;
        }

        const publicKey = sortedPublicKeys[index];
        arr.push(publicKey);

        return arr;
      }, []);

    if (remoteItem.signatureType === SignatureType.INTERMEDIATE) {
      for (const publicKey of remoteItem.signaturesMap.keys()) {
        const signature = remoteItem.signaturesMap.get(publicKey);
        const isValid = partialSignatureVerify(signature, publicKey, hash);
        if (!isValid) {
          return null;
        }
      }
    } else {
      const calcMultiPublicKey = buildSharedPublicKeyX(involvedPublicKeys, hash);
      const multiPublicKey = [...remoteItem.signaturesMap.keys()][0];

      if (calcMultiPublicKey !== multiPublicKey) {
        return null;
      }

      const multisig = remoteItem.signaturesMap.get(multiPublicKey);
      const isValid = verify(multisig, multiPublicKey);
      if (!isValid) {
        return null;
      }
    }

    const timestamp = Date.now();
    const timestampIndex = [...this.db.values()].filter((v) => v.timestamp === timestamp).length;

    /** object is mutated here, so no need to save it to map * */
    let dbItem: DbItem = this.getDbItem(hash);

    if (dbItem && dbItem.signatureType === SignatureType.MULTISIG && remoteItem.signatureType === SignatureType.INTERMEDIATE) {
      return null;
    }

    if (dbItem && dbItem.signatureType === SignatureType.MULTISIG && remoteItem.signatureType === SignatureType.MULTISIG) {
      const localMultiSigPublicKey = [...dbItem.signaturesMap.keys()][0];
      const remoteMultiSigPublicKey = [...remoteItem.signaturesMap.keys()][0];

      if (localMultiSigPublicKey === remoteMultiSigPublicKey || localMultiSigPublicKey > remoteMultiSigPublicKey) {
        this.updatePeerNodeLastTimestamp(peerNode, remoteItem.timestamp, remoteItem.timestampIndex);
        return null;
      }

      const remoteMultiSig = remoteItem.signaturesMap.get(remoteMultiSigPublicKey);

      dbItem.signaturesMap = new Map<string, string>();
      dbItem.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
      dbItem.publicKeys = new Set<string>(involvedPublicKeys);
      dbItem.stateHash = remoteItem.stateHash;
      dbItem.timestamp = timestamp;
      dbItem.timestampIndex = timestampIndex;

      this.saveItem(dbItem, peerNode, remoteItem.timestamp, remoteItem.timestampIndex);
      this.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    if (remoteItem.signatureType === SignatureType.MULTISIG) {
      const remoteMultiSigPublicKey = [...remoteItem.signaturesMap.keys()][0];
      const remoteMultiSig = remoteItem.signaturesMap.get(remoteMultiSigPublicKey);

      if (!dbItem) {
        dbItem = DbItem.fromPlainObject({
          hash: remoteItem.hash,
          stateHash: remoteItem.stateHash,
          timestamp,
          timestampIndex,
          key: remoteItem.key,
          value: remoteItem.value,
          version: remoteItem.version,
          signaturesMap: Object.fromEntries(remoteItem.signaturesMap),
          signatureType: SignatureType.MULTISIG,
          publicKeys: involvedPublicKeys
        });
      } else {
        dbItem.stateHash = remoteItem.stateHash;
        dbItem.timestamp = timestamp;
        dbItem.timestampIndex = timestampIndex;
        dbItem.signaturesMap = new Map<string, string>();
        dbItem.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
        dbItem.publicKeys = new Set<string>(involvedPublicKeys);
        dbItem.signatureType = SignatureType.MULTISIG;
      }

      this.saveItem(dbItem, peerNode, remoteItem.timestamp, remoteItem.timestampIndex);
      this.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    if (!dbItem) {
      dbItem = DbItem.fromPlainObject({
        hash: remoteItem.hash,
        stateHash: remoteItem.stateHash,
        timestamp,
        timestampIndex,
        key: remoteItem.key,
        value: remoteItem.value,
        version: remoteItem.version,
        signaturesMap: Object.fromEntries(remoteItem.signaturesMap),
        signatureType: SignatureType.INTERMEDIATE,
        publicKeys: involvedPublicKeys
      });

      const signature = buildPartialSignature(
        this.privateKey,
        hash
      );

      dbItem.signaturesMap.set(this.publicKey, signature);
      dbItem.publicKeys.add(this.publicKey);
      dbItem.stateHash = this.hashData(`${dbItem.hash}:${dbItem.value}:${dbItem.version}${dbItem.publicKeys.size}`);
    } else {
      for (const publicKey of remoteItem.signaturesMap.keys()) {
        const signature = remoteItem.signaturesMap.get(publicKey);
        dbItem.signaturesMap.set(publicKey, signature);
        dbItem.publicKeys.add(publicKey);
      }

      dbItem.timestamp = timestamp;
      dbItem.timestampIndex = timestampIndex;
      dbItem.stateHash = this.hashData(`${dbItem.hash}:${dbItem.value}:${dbItem.version}${dbItem.publicKeys.size}`);
    }

    if (dbItem.signaturesMap.size >= this.majority()) {
      const publicKeysForMusig = [...dbItem.signaturesMap.keys()].sort().slice(0, this.majority());
      const totalPublicKeys = dbItem.publicKeys.size;
      const signaturesForMusig = publicKeysForMusig.map((publicKey) => dbItem.signaturesMap.get(publicKey));
      const multiPublicKey = buildSharedPublicKeyX(publicKeysForMusig, hash);

      const multiSignature = buildSharedSignature(signaturesForMusig);
      dbItem.signaturesMap = new Map<string, string>();
      dbItem.signaturesMap.set(multiPublicKey, multiSignature);
      dbItem.signatureType = SignatureType.MULTISIG;
      dbItem.publicKeys = new Set<string>(publicKeysForMusig);
      dbItem.stateHash = this.hashData(`${dbItem.hash}:${dbItem.value}:${dbItem.version}${totalPublicKeys + 1}`);
    }

    this.saveItem(dbItem, peerNode, remoteItem.timestamp, remoteItem.timestampIndex);
    this.emit(EventTypes.STATE_UPDATE);
  }

  private saveItem(item: DbItem, peerNode?: NodeModel, peerTimestamp?: number, peerTimestampIndex?: number) {
    const prevItem = this.getDbItem(item.hash);

    this.setDbItem(item);
    this.lastUpdateTimestamp = item.timestamp;
    this.lastUpdateTimestampIndex = item.timestampIndex;

    if (peerNode) {
      this.updatePeerNodeLastTimestamp(peerNode, peerTimestamp, peerTimestampIndex);
    }

    if (
      item.signatureType === SignatureType.MULTISIG &&
      ((prevItem && prevItem.signatureType === SignatureType.INTERMEDIATE) || !prevItem)
    ) {
      this.stateRoot = new BN(this.stateRoot, 16).add(new BN(item.stateHash, 16)).mod(ec.n).toString(16);
    }
  }

  private updatePeerNodeLastTimestamp(peerNode?: NodeModel, peerTimestamp?: number, peerTimestampIndex?: number) {
    // eslint-disable-next-line no-param-reassign
    peerNode.lastUpdateTimestamp = peerTimestamp;
    // eslint-disable-next-line no-param-reassign
    peerNode.lastUpdateTimestampIndex = peerTimestampIndex;
  }

  // eslint-disable-next-line no-unused-vars
  public write(address: string, packet: Buffer): void {
    throw new Error('should be implemented!');
  }
}

export { NodeModel };
