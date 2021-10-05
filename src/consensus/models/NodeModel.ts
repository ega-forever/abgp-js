import { EventEmitter } from 'events';
import { MerkleTree } from 'merkletreejs';
import crypto from 'crypto';
import { buildPartialSignature, buildSharedSignature } from '../utils/cryptoUtils';
import SignatureType from '../constants/SignatureType';

export class StateItem {
  key: string;
  value: string;
  version: number;
  signature: string;
  signatureType: number;
}

export class DbItem {
  key: string;
  value: string;
  version: number;
  signatures: string[];
  multisignature: string;
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
  public publicKeysCombinationsInQuorum: string[][];
  public readonly privateKey: string;
  public readonly publicKey: string;
  public merkleTree: MerkleTree;
  public vectorClock: number;

  public readonly nodes: Map<string, NodeModel> = new Map<string, NodeModel>();
  public readonly state: Map<string, StateItem>; // should be map <string, merkleTree> todo also store version - signatures
  public readonly db: Map<string, DbItem>;
  private readonly nodeAddress: string;

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
    this.vectorClock = 0;
  }

  public hashData(data: string) {
    return crypto.createHash('sha256')
      .update(data)
      .digest('hex');
  }

  public majority() { //todo majority should be set in config, and node links should be checked by majority
    return Math.ceil(this.nodes.size / 2) + 1;
  }

  public getStateRoot() {
    return this.merkleTree.getHexRoot();
  }

  public getStateMerkleDepth() {
    return this.merkleTree.getDepth()
  }

  public getLayersAtDepth(index: number) {
    const layers = this.merkleTree.getHexLayers();
    return layers[layers.length - index - 1];
  }

  public getLayers(): string[][] {
    return this.merkleTree.getHexLayers() as any;
  }

  public getLayerLeaves(leave: string) {
    const layers = this.merkleTree.getHexLayers();
    const currentLayerIndex = layers.findIndex(l => l.includes(leave));

    if (currentLayerIndex === -1 || currentLayerIndex === layers.length - 1) {
      return null;
    }

    const currentLayer = layers[currentLayerIndex];
    const currentPosition = currentLayer.indexOf(leave);
    const nextLayer = layers[currentLayerIndex - 1];
    return nextLayer.slice(currentPosition * 2, currentPosition * 2 + 2);
  }

  public append(key: string, value: string, version: number = 1) {
    const hash = this.hashData(`${key}:${value}:${version}`);
    const signature = buildPartialSignature(
      this.privateKey,
      hash
    );

    let stateItem: StateItem;

    /** object is mutated here, so no need to save it to map **/
    const dbItem = this.db.get(`0x${hash}`) || {
      key,
      value,
      version,
      signatures: [],
      multisignature: null
    };

    dbItem.signatures.push(signature);

    if (dbItem.signatures.length === this.majority()) {
      dbItem.multisignature = buildSharedSignature(dbItem.signatures);
      this.shakeTree(key, version);
      stateItem = {
        key,
        value,
        version,
        signature: dbItem.multisignature,
        signatureType: SignatureType.MULTISIG
      };
    } else {
      stateItem = {
        key,
        value,
        version,
        signature: signature,
        signatureType: SignatureType.INTERMEDIATE
      };
    }

    const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`)
    this.state.set(`0x${leaveHash}`, stateItem);
    const leaves = new Array(...this.state.keys());
    this.merkleTree = new MerkleTree(leaves, this.hashData);
    this.vectorClock++;
  }

  public remoteAppend(item: StateItem){

    const hash = this.hashData(`${item.key}:${item.value}:${item.version}`);
    const signature = buildPartialSignature(
      this.privateKey,
      hash
    );

    let stateItem: StateItem;

    /** object is mutated here, so no need to save it to map **/
    const dbItem = this.db.get(`0x${hash}`) || {
      key: item.key,
      value: item.value,
      version: item.version,
      signatures: [],
      multisignature: null
    };

    dbItem.signatures.push(item.signature);
    dbItem.signatures.push(signature);

    if (dbItem.signatures.length === this.majority()) {
      dbItem.multisignature = buildSharedSignature(dbItem.signatures);
      this.shakeTree(item.key, item.version);
      stateItem = {
        key,
        value,
        version,
        signature: dbItem.multisignature,
        signatureType: SignatureType.MULTISIG
      };
    } else {
      stateItem = {
        key,
        value,
        version,
        signature: signature,
        signatureType: SignatureType.INTERMEDIATE
      };
    }

    const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`)
    this.state.set(`0x${leaveHash}`, stateItem);
    const leaves = new Array(...this.state.keys());
    this.merkleTree = new MerkleTree(leaves, this.hashData);
    this.vectorClock++;
  }

/*
  private updateState(item: StateItem){
    if (dbItem.signatures.length === this.majority()) {
      dbItem.multisignature = buildSharedSignature(dbItem.signatures);
      this.shakeTree(key, version);
      stateItem = {
        key,
        value,
        version,
        signature: dbItem.multisignature,
        signatureType: SignatureType.MULTISIG
      };
    } else {
      stateItem = {
        key,
        value,
        version,
        signature: signature,
        signatureType: SignatureType.INTERMEDIATE
      };
    }

    const leaveHash = this.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}:${stateItem.signature}`)
    this.state.set(`0x${leaveHash}`, stateItem);
    const leaves = new Array(...this.state.keys());
    this.merkleTree = new MerkleTree(leaves, this.hashData);
    this.vectorClock++;
  }
*/

  public shakeTree(key: string, version: number) {
    const intermediateHashes = this.getStateHashesByKey(key, version, SignatureType.INTERMEDIATE);
    for (const hash of intermediateHashes) {
      this.state.delete(hash);
    }
    this.vectorClock++;
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
