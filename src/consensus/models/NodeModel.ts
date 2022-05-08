import { EventEmitter } from 'events';
import { IStorageInterface } from '../interfaces/IStorageInterface';
import StateModel from './StateModel';

export default class NodeModel extends EventEmitter {
  get address(): string {
    return this.nodeAddress;
  }

  public readonly privateKey: string;

  public readonly publicKey: string;

  private readonly nodeAddress: string;

  public readonly storage: IStorageInterface;

  public constructor(
    privateKey: string,
    multiaddr: string,
    storage: IStorageInterface
  ) {
    super();
    this.privateKey = privateKey;
    this.publicKey = multiaddr.match(/\w+$/).toString();
    this.nodeAddress = multiaddr.split(/\w+$/)[0].replace(/\/$/, '');
    this.storage = storage;
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

  // eslint-disable-next-line no-unused-vars
  public write(address: string, packet: Buffer): void {
    throw new Error('should be implemented!');
  }
}
