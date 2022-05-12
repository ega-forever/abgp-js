import EventTypes from '../constants/EventTypes';
import MessageTypes from '../constants/MessageTypes';
import ABGP from '../main';
import NodeModel from '../models/NodeModel';
import PacketModel from '../models/PacketModel';
import MessageApi from './MessageApi';

export default class NodeApi {
  private readonly abgp: ABGP;

  private readonly messageApi: MessageApi;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
    this.messageApi = new MessageApi(abgp);
  }

  public join(multiaddr: string): NodeModel {
    const publicKey = multiaddr.match(/\w+$/).toString();

    if (this.abgp.publicKey === publicKey) {
      return;
    }

    const node = new NodeModel(null, multiaddr, this.abgp.storage);
    this.abgp.publicKeys.add(node.publicKey);
    node.once('end', () => this.leave(node.publicKey));

    this.abgp.nodes.set(publicKey, node);
    this.abgp.emit(EventTypes.NODE_JOIN, node);
    return node;
  }

  public leave(publicKey: string): void {
    const node = this.abgp.nodes.get(publicKey);
    this.abgp.nodes.delete(publicKey);
    this.abgp.emit(EventTypes.NODE_LEAVE, node);
  }

  public validatePacket(packet: PacketModel) {
    if (!this.abgp.nodes.has(packet.publicKey) || packet.lastUpdateTimestamp > Date.now()) {
      return null;
    }

    return packet;
  }

  public async dataRequest(packet: PacketModel) {
    const publicKeys = [...this.abgp.publicKeys.keys()].sort();
    this.abgp.logger.trace(`requesting records for node [${packet.publicKey}] with timestamp ${packet.lastUpdateTimestamp}`);
    const records = await this.abgp.storage.Record.getAfterTimestamp(packet.data.lastUpdateTimestamp, packet.data.lastUpdateTimestampIndex, this.abgp.batchReplicationSize);
    const data = records.map((v) => v.toPlainObject(publicKeys));
    return this.messageApi.packet(MessageTypes.DATA_REP, {
      data
    });
  }
}
