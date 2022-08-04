import MessageApi from '../api/MessageApi';
import NodeApi from '../api/NodeApi';
import ABGP from '../main';
import PacketModel from '../models/PacketModel';
import MessageTypes from '../constants/MessageTypes';

export default class RequestProcessorService {
  private readonly abgp: ABGP;

  private readonly messageApi: MessageApi;

  private readonly nodeApi: NodeApi;

  // eslint-disable-next-line no-unused-vars
  private readonly actionMap: Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>;

  constructor(abgp: ABGP) {
    this.messageApi = new MessageApi(abgp);
    this.nodeApi = new NodeApi(abgp);
    this.abgp = abgp;
    // eslint-disable-next-line no-unused-vars
    this.actionMap = new Map<number, Array<(packet: PacketModel) => Promise<PacketModel>>>();

    this.actionMap.set(MessageTypes.DATA_REQ, [
      this.nodeApi.validatePacket.bind(this.nodeApi),
      this.nodeApi.dataRequest.bind(this.nodeApi)
    ]);
  }

  public async process(packet: PacketModel): Promise<PacketModel> {
    const node = this.abgp.nodes.get(packet.publicKey);

    if (!node || !this.actionMap.has(packet.type)) {
      return this.abgp.messageApi.packet(MessageTypes.ERR);
    }

    let reply: PacketModel | null | false = false;

    for (const action of this.actionMap.get(packet.type)) {
      if (reply === null) {
        continue;
      }
      reply = await action(reply === false ? packet : reply);
    }

    if (!reply) {
      return this.abgp.messageApi.packet(MessageTypes.ERR);
    }

    return reply;
  }
}
