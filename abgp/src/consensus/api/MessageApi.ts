import ABGP from '../main';
import PacketModel from '../models/PacketModel';

export default class MessageApi {
  private abgp: ABGP;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
  }

  public async message(packet: PacketModel, nodePublicKey: string): Promise<PacketModel> {
    const middlewaredReqPacket = await this.abgp.reqMiddleware(packet);
    const node = this.abgp.nodes.get(nodePublicKey);
    const reply = await this.abgp.call(node.address, middlewaredReqPacket);
    const middlewaredResPacket = await this.abgp.resMiddleware(reply, nodePublicKey);
    return middlewaredResPacket;
  }

  public async packet(type: number, data: any = null): Promise<PacketModel> {
    const state = await this.abgp.getState();
    return new PacketModel(
      state.root,
      this.abgp.publicKey,
      type,
      state.timestamp,
      state.timestampIndex,
      data
    );
  }

  public decodePacket(message: string): PacketModel {
    return JSON.parse(message);
  }
}
