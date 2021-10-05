import { MessageApi } from '../api/MessageApi';
import { NodeApi } from '../api/NodeApi';
import messageTypes from '../constants/MessageTypes';
import { BGP } from '../main';
import { PacketModel } from '../models/PacketModel';

class RequestProcessorService {

  private readonly bgp: BGP;
  private readonly messageApi: MessageApi;
  private readonly nodeApi: NodeApi;

  private readonly actionMap: Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>;

  constructor(bgp: BGP) {
    this.messageApi = new MessageApi(bgp);
    this.nodeApi = new NodeApi(bgp);
    this.bgp = bgp;
    this.actionMap = new Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>();

    this.actionMap.set(messageTypes.STATE_REQ, [
      this.nodeApi.stateRequest.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.STATE_REP, [
      this.nodeApi.stateResponse.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.DATA_REQ, [
      this.nodeApi.dataRequest.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.DATA_REP, [
      this.nodeApi.dataResponse.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.ACK, [
      this.nodeApi.validateState.bind(this.nodeApi)
    ]);
  }

  public async process(packet: PacketModel) {

    const node = this.bgp.nodes.get(packet.publicKey);

    if (!node || !this.actionMap.has(packet.type))
      return;

    let reply: PacketModel | null | false = false;

    for (const action of this.actionMap.get(packet.type)) {
      if (reply === null) {
        continue;
      }
      reply = await action(reply === false ? packet : reply);
    }

    if (reply)
      await this.messageApi.message(reply, packet.publicKey);
  }

}

export { RequestProcessorService };
