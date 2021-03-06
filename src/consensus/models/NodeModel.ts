import { EventEmitter } from 'events';
import { IStorageInterface } from '../interfaces/IStorageInterface';
import StateModel from './StateModel';
import ICryptoInterface from '../interfaces/ICryptoInterface';

export default class NodeModel extends EventEmitter {
  get address(): string {
    return this.nodeAddress;
  }

  public readonly privateKey: string;

  public readonly publicKey: string;

  private readonly nodeAddress: string;

  public readonly storage: IStorageInterface;

  public readonly crypto: ICryptoInterface;

  public constructor(
    privateKey: string,
    multiaddr: string,
    storage: IStorageInterface,
    crypto: ICryptoInterface
  ) {
    super();
    this.privateKey = privateKey;
    this.publicKey = multiaddr.match(/\w+$/).toString();
    this.nodeAddress = multiaddr.split(/\w+$/)[0].replace(/\/$/, '');
    this.storage = storage;
    this.crypto = crypto;
  }

  public async getState(): Promise<StateModel> {
    const state = await this.storage.State.get(this.publicKey);

    if (state) {
      return state;
    }

    return {
      timestamp: 0,
      timestampIndex: -1,
      root: '0',
      publicKey: this.publicKey
    };
  }

  public async saveState(timestamp: number, timestampIndex: number, root: string) {
    await this.storage.State.save({
      timestamp,
      timestampIndex,
      root,
      publicKey: this.publicKey
    });
  }
}
