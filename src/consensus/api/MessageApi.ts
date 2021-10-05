import { PacketModel } from '../models/PacketModel';
import { BGP } from '../main';

class MessageApi {

  private bgp: BGP;

  constructor(bgp: BGP) {
    this.bgp = bgp;
  }

  public async message(packet: PacketModel, peerPublicKey: string) {
    packet = await this.bgp.resMiddleware(packet, peerPublicKey);
    const node = this.bgp.nodes.get(peerPublicKey);
    await node.write(node.address, Buffer.from(JSON.stringify(packet)));
  }

  public packet(type: number, data: any = null): PacketModel {
    return new PacketModel(
      this.bgp.getStateRoot(),
      this.bgp.publicKey,
      type,
      this.bgp.vectorClock,
      data);
  }

  public decodePacket(message: Buffer): PacketModel {
    return JSON.parse(message.toString());
  }

}

export { MessageApi };
