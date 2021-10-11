import crypto from 'crypto';
import { EventEmitter } from 'events';
import { MerkleTree } from 'merkletreejs';
import EventTypes from '../constants/EventTypes';
import SignatureType from '../constants/SignatureType';
import {
  buildPartialSignature, buildPublicKeysRoot,
  buildSharedPublicKeyX,
  buildSharedSignature,
  partialSignatureVerify, verify
} from '../utils/cryptoUtils';

export class DataItem {
  public hash: string;
  public key: string;
  public value: string;
  public version: number;
  public signaturesMap: Object; // <string, string>
  public signatureType: number;
  public publicKeyMap: number;
}

export class StateItem {
  public key: string;
  public value: string;
  public version: number;
  public signature: string;
  public signatureType: number;
}

export class DbItem {
  public key: string;
  public value: string;
  public version: number;
  public signaturesMap: Map<string, string>; // signature to public key
  public signatureType: number;
  public publicKeys: Set<string>;
}

class NodeModel extends EventEmitter {

  get address(): string {
    return this.nodeAddress;
  }

  public gossipInterval: {
    min: number,
    max: number
  };
  public sendSignalToRandomPeer: boolean;
  public readonly privateKey: string;
  public readonly publicKey: string;
  public merkleTree: MerkleTree;
  public dataUpdateTimestamp: number;
  public nextDataUpdateTimestamp: number;

  public readonly nodes: Map<string, NodeModel> = new Map<string, NodeModel>();
  public readonly state: Map<string, StateItem>;
  public readonly db: Map<string, DbItem>;
  private readonly nodeAddress: string;
  public readonly publicKeys: Set<string>

  public constructor(
    privateKey: string,
    multiaddr: string
  ) {
    super();
    this.privateKey = privateKey;
    this.publicKey = multiaddr.match(/\w+$/).toString();
    this.nodeAddress = multiaddr.split(/\w+$/)[0].replace(/\/$/, '');
    this.state = new Map<string, StateItem>();
    this.merkleTree = new MerkleTree([], this.hashData);
    this.db = new Map<string, DbItem>();
    this.dataUpdateTimestamp = 0;
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

  public getStateRoot() {
    return this.merkleTree.getHexRoot();
  }

  public getLayers(): string[][] {
    return this.merkleTree.getHexLayers() as any;
  }

  public append(key: string, value: string, version: number = 1) {
    const hash = this.hashData(`${key}:${value}:${version}`);

    if (this.db.has(`0x${hash}`)) {
      return;
    }

    const signature = buildPartialSignature(
      this.privateKey,
      hash
    );

    const stateItem: StateItem = {
      key,
      value,
      version,
      signature,
      signatureType: SignatureType.INTERMEDIATE
    };

    const signaturesMap = new Map<string, string>();
    signaturesMap.set(this.publicKey, signature);

    const dbItem: DbItem = {
      key,
      value,
      version,
      signaturesMap,
      signatureType: SignatureType.INTERMEDIATE,
      publicKeys: new Set<string>(this.publicKey)
    };

    this.db.set(`0x${hash}`, dbItem);
    const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`);
    this.state.set(`0x${leaveHash}`, stateItem);
    this.dataUpdateTimestamp = Date.now();
    this.rebuildTree();
    this.emit(EventTypes.STATE_UPDATE);
  }

  public remoteAppend(item: DataItem) {
    const hash = this.hashData(`${item.key}:${item.value}:${item.version}`);

    const sortedPublicKeys = [...this.publicKeys.keys()].sort();
    const involvedPublicKeys: string[] = item.publicKeyMap.toString(2)
      .padStart(this.publicKeys.size, '0')
      .split('')
      .reduce((arr, elem, index) => {
        if (elem === '0') {
          return arr;
        }

        const publicKey = sortedPublicKeys[index];
        arr.push(publicKey)

        return arr;
      }, []);

    if (item.signatureType === SignatureType.INTERMEDIATE) {
      for (const publicKey of Object.keys(item.signaturesMap)) {
        const signature = item.signaturesMap[publicKey];
        const isValid = partialSignatureVerify(signature, publicKey, hash);
        if (!isValid) {
          return null;
        }
      }
    } else {
      const calcMultiPublicKey = buildSharedPublicKeyX(involvedPublicKeys, hash);
      const multiPublicKey = Object.keys(item.signaturesMap)[0];

      if (calcMultiPublicKey !== multiPublicKey) {
        return null;
      }

      const multisig = item.signaturesMap[multiPublicKey];
      const isValid = verify(multisig, multiPublicKey);
      if (!isValid) {
        return null;
      }
    }


    /** object is mutated here, so no need to save it to map **/
    const dbItem: DbItem = this.db.get(`0x${hash}`) || {
      key: item.key,
      value: item.value,
      version: item.version,
      signaturesMap: new Map<string, string>(),
      signatureType: SignatureType.INTERMEDIATE,
      publicKeys: new Set<string>(involvedPublicKeys)
    };

    if (dbItem.signatureType === SignatureType.MULTISIG && item.signatureType === SignatureType.INTERMEDIATE) {
      return null;
    }

    if (dbItem.signatureType === SignatureType.MULTISIG && item.signatureType === SignatureType.MULTISIG) {

      const localMultiSigPublicKey = [...dbItem.signaturesMap.keys()][0];
      const remoteMultiSigPublicKey = Object.keys(item.signaturesMap)[0];

      if (localMultiSigPublicKey === remoteMultiSigPublicKey || localMultiSigPublicKey > remoteMultiSigPublicKey) {
        return null;
      }

      const localMultiSig = dbItem.signaturesMap.get(localMultiSigPublicKey);
      const remoteMultiSig = item.signaturesMap[remoteMultiSigPublicKey];

      const oldLeaveHash = this.hashData(`${item.key}:${item.value}:${item.version}:${localMultiSig}`);
      this.state.delete(`0x${oldLeaveHash}`);

      dbItem.signaturesMap = new Map<string, string>();
      dbItem.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
      dbItem.publicKeys = new Set<string>(involvedPublicKeys);
      this.db.set(`0x${hash}`, dbItem);

      const leaveHash = this.hashData(`${item.key}:${item.value}:${item.version}:${remoteMultiSig}`);
      const stateItem: StateItem = {
        key: item.key,
        value: item.value,
        version: item.version,
        signature: remoteMultiSig,
        signatureType: SignatureType.MULTISIG
      };

      this.state.set(`0x${leaveHash}`, stateItem);
      this.dataUpdateTimestamp = Date.now();
      this.rebuildTree();
      this.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    if (item.signatureType === SignatureType.MULTISIG) {
      dbItem.signaturesMap = new Map<string, string>();

      const remoteMultiSigPublicKey = Object.keys(item.signaturesMap)[0];
      const remoteMultiSig = item.signaturesMap[remoteMultiSigPublicKey];

      dbItem.signaturesMap.set(remoteMultiSigPublicKey, remoteMultiSig);
      dbItem.publicKeys = new Set<string>(involvedPublicKeys);
      dbItem.signatureType = SignatureType.MULTISIG;

      const stateItem: StateItem = {
        key: item.key,
        value: item.value,
        version: item.version,
        signature: remoteMultiSig,
        signatureType: SignatureType.MULTISIG
      };

      this.db.set(`0x${hash}`, dbItem);
      const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`);
      this.state.set(`0x${leaveHash}`, stateItem);
      this.dataUpdateTimestamp = Date.now();
      this.removeIntermediateStateItems(item.key, item.version);
      this.rebuildTree();
      this.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    const signature = buildPartialSignature(
      this.privateKey,
      hash
    );

    dbItem.signaturesMap.set(this.publicKey, signature);
    dbItem.publicKeys.add(this.publicKey);

    for (const publicKey of Object.keys(item.signaturesMap)) {
      const signature = item.signaturesMap[publicKey];
      dbItem.signaturesMap.set(publicKey, signature);
      dbItem.publicKeys.add(publicKey);
    }

    if (dbItem.signaturesMap.size >= this.majority()) {
      const publicKeysForMusig = [...dbItem.signaturesMap.keys()].sort().slice(0, this.majority());
      const signaturesForMusig = publicKeysForMusig.map((publicKey) => dbItem.signaturesMap.get(publicKey));
      const multiPublicKey = buildSharedPublicKeyX(publicKeysForMusig, hash);

      const multiSignature = buildSharedSignature(signaturesForMusig);
      dbItem.signaturesMap = new Map<string, string>();
      dbItem.signaturesMap.set(multiPublicKey, multiSignature);
      dbItem.signatureType = SignatureType.MULTISIG;

      const stateItem: StateItem = {
        key: item.key,
        value: item.value,
        version: item.version,
        signature: multiSignature,
        signatureType: SignatureType.MULTISIG
      };

      this.db.set(`0x${hash}`, dbItem);
      const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`);
      this.state.set(`0x${leaveHash}`, stateItem);
      this.dataUpdateTimestamp = Date.now();
      this.removeIntermediateStateItems(item.key, item.version);
      this.rebuildTree();
      this.emit(EventTypes.STATE_UPDATE);
      return null;
    }

    for (const signature of dbItem.signaturesMap.values()) {
      const stateItem: StateItem = {
        key: item.key,
        value: item.value,
        version: item.version,
        signature,
        signatureType: SignatureType.INTERMEDIATE
      };

      const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`);
      this.state.set(`0x${leaveHash}`, stateItem);
      this.dataUpdateTimestamp = Date.now();
    }

    this.db.set(`0x${hash}`, dbItem);
    this.rebuildTree();
    this.emit(EventTypes.STATE_UPDATE);
  }

  public removeIntermediateStateItems(key: string, version: number) {
    const intermediateHashes = this.getStateHashesByKey(key, version, SignatureType.INTERMEDIATE);
    for (const hash of intermediateHashes) {
      this.state.delete(hash);
      this.dataUpdateTimestamp = Date.now();
    }
  }

  public rebuildTree() {
    const leaves = new Array(...this.state.keys()).sort();
    this.merkleTree = new MerkleTree(leaves, this.hashData);
  }

  public getStateHashesByKey(key: string, version: number, signatureType: number) {
    const hashes = [];
    for (const hash of this.state.keys()) {
      const item = this.state.get(hash);
      if (item.key === key && item.version === version && item.signatureType === signatureType) {
        hashes.push(hash);
      }
    }

    return hashes;
  }

  public write(address: string, packet: Buffer): void {
    throw new Error('should be implemented!');
  }

}

export { NodeModel };
