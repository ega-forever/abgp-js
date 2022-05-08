import ABGP from '../main';
import PacketModel from '../models/PacketModel';

export default class MessageApi {
  private abgp: ABGP;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
  }

  public async message(packet: PacketModel, peerPublicKey: string) {
    const middlewaredPacket = await this.abgp.resMiddleware(packet, peerPublicKey);
    const node = this.abgp.nodes.get(peerPublicKey);
    await node.write(node.address, Buffer.from(JSON.stringify(middlewaredPacket)));
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

  public decodePacket(message: Buffer): PacketModel {
    return JSON.parse(message.toString());
  }
}
