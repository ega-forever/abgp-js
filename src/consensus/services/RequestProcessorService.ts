import { MessageApi } from '../api/MessageApi';
import { NodeApi } from '../api/NodeApi';
import messageTypes from '../constants/MessageTypes';
import { ABGP } from '../main';
import { PacketModel } from '../models/PacketModel';

class RequestProcessorService {

  private readonly abgp: ABGP;
  private readonly messageApi: MessageApi;
  private readonly nodeApi: NodeApi;

  private readonly actionMap: Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>;

  constructor(abgp: ABGP) {
    this.messageApi = new MessageApi(abgp);
    this.nodeApi = new NodeApi(abgp);
    this.abgp = abgp;
    this.actionMap = new Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>();

    this.actionMap.set(messageTypes.STATE_REQ, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.stateRequest.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.STATE_REP, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.stateResponse.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.DATA_REQ, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.dataRequest.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.DATA_REP, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.dataResponse.bind(this.nodeApi)
    ]);

    this.actionMap.set(messageTypes.ACK, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.validateState.bind(this.nodeApi)
    ]);
  }

  public async process(packet: PacketModel) {

    const node = this.abgp.nodes.get(packet.publicKey);

    if (!node || !this.actionMap.has(packet.type))
      return;

    let reply: PacketModel | null | false = false;

    for (const action of this.actionMap.get(packet.type)) {
      if (reply === null) {
        continue;
      }
      reply = await action(reply === false ? packet : reply);
    }

    return reply;
  }

}

export { RequestProcessorService };
