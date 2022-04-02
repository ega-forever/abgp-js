import { ABGP } from '../main';
import { PacketModel } from '../models/PacketModel';

class MessageApi {

  private abgp: ABGP;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
  }

  public async message(packet: PacketModel, peerPublicKey: string) {
    packet = await this.abgp.resMiddleware(packet, peerPublicKey);
    const node = this.abgp.nodes.get(peerPublicKey);
    await node.write(node.address, Buffer.from(JSON.stringify(packet)));
  }

  public packet(type: number, data: any = null): PacketModel {
    return new PacketModel(
      this.abgp.getStateRoot(),
      this.abgp.publicKey,
      type,
      this.abgp.lastUpdateTimestamp,
      this.abgp.lastUpdateTimestampIndex,
      data);
  }

  public decodePacket(message: Buffer): PacketModel {
    return JSON.parse(message.toString());
  }

}

export { MessageApi };
