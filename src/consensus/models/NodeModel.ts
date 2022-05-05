import { EventEmitter } from 'events';

export default class NodeModel extends EventEmitter {
  get address(): string {
    return this.nodeAddress;
  }

  public readonly privateKey: string;

  public readonly publicKey: string;

  public stateRoot: string;

  public lastUpdateTimestamp: number;

  public lastUpdateTimestampIndex: number;

  private readonly nodeAddress: string;

  public constructor(
    privateKey: string,
    multiaddr: string
  ) {
    super();
    this.privateKey = privateKey;
    this.publicKey = multiaddr.match(/\w+$/).toString();
    this.nodeAddress = multiaddr.split(/\w+$/)[0].replace(/\/$/, '');
    this.lastUpdateTimestamp = 0;
    this.lastUpdateTimestampIndex = 0;
    this.stateRoot = '0';
  }

  public getStateRoot() {
    return this.stateRoot;
  }

  // todo function to update state root from AppendApi

  // eslint-disable-next-line no-unused-vars
  public write(address: string, packet: Buffer): void {
    throw new Error('should be implemented!');
  }
}
