class PacketModel {

  public root: string;
  public publicKey: string;
  public type: number;
  public data: any;
  public dataUpdateTimestamp: number;
  public timestamp: number;

  constructor(
    root: string,
    publicKey: string,
    type: number,
    dataUpdateTimestamp: number,
    data: any = null
    ) {
    this.root = root;
    this.type = type;
    this.publicKey = publicKey;
    this.dataUpdateTimestamp = dataUpdateTimestamp;
    this.data = data;
    this.timestamp = Date.now();
  }

}

export { PacketModel };
