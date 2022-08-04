export default class PacketModel {
  public root: string;

  public publicKey: string;

  public type: number;

  public data: any;

  public lastUpdateTimestamp: number;

  public lastUpdateTimestampIndex: number;

  public timestamp: number;

  constructor(
    root: string,
    publicKey: string,
    type: number,
    lastUpdateTimestamp: number,
    lastUpdateTimestampIndex: number,
    data: any = null
  ) {
    this.root = root;
    this.type = type;
    this.publicKey = publicKey;
    this.lastUpdateTimestamp = lastUpdateTimestamp;
    this.lastUpdateTimestampIndex = lastUpdateTimestampIndex;
    this.data = data;
    this.timestamp = Date.now();
  }
}
