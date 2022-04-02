import eventTypes from '../constants/EventTypes';
import EventTypes from '../constants/EventTypes';
import MessageTypes from '../constants/MessageTypes';
import { ABGP } from '../main';
import { DbItem, NodeModel } from '../models/NodeModel';
import { PacketModel } from '../models/PacketModel';
import { MessageApi } from './MessageApi';

class NodeApi {

  private readonly abgp: ABGP;
  private messageApi: MessageApi;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
    this.messageApi = new MessageApi(abgp);
  }

  public join(multiaddr: string): NodeModel {

    const publicKey = multiaddr.match(/\w+$/).toString();

    if (this.abgp.publicKey === publicKey)
      return;

    const node = new NodeModel(null, multiaddr);
    this.abgp.publicKeys.add(node.publicKey);

    node.write = this.abgp.write.bind(this.abgp);
    node.once('end', () => this.leave(node.publicKey));

    this.abgp.nodes.set(publicKey, node);
    this.abgp.emit(eventTypes.NODE_JOIN, node);
    return node;
  }

  public leave(publicKey: string): void {

    const node = this.abgp.nodes.get(publicKey);
    this.abgp.nodes.delete(publicKey);
    this.abgp.emit(eventTypes.NODE_LEAVE, node);
  }

  public validatePacket(packet: PacketModel) {
    if (!this.abgp.nodes.has(packet.publicKey) || packet.lastUpdateTimestamp > Date.now()) {
      return null;
    }

    return packet;
  }

  public validateState(packet: PacketModel) {

    const peerNode = this.abgp.nodes.get(packet.publicKey);

    if ( // todo add validation by state hash
      peerNode.lastUpdateTimestamp === packet.lastUpdateTimestamp &&
      peerNode.lastUpdateTimestampIndex === packet.lastUpdateTimestampIndex) {
      this.abgp.emit(EventTypes.STATE_SYNCED, packet.publicKey);
      return null;
    }

    return this.messageApi.packet(MessageTypes.DATA_REQ, {
      lastUpdateTimestamp: peerNode.lastUpdateTimestamp,
      lastUpdateTimestampIndex: peerNode.lastUpdateTimestampIndex
    });
  }

  public dataRequest(packet: PacketModel) {
    const publicKeys = [...this.abgp.publicKeys.keys()];

    const data = [...this.abgp.db.values()]
      .filter(v=>
        v.timestamp > packet.data.lastUpdateTimestamp ||
        (v.timestamp === packet.data.lastUpdateTimestamp && v.timestampIndex > packet.data.lastUpdateTimestampIndex)
      )
     // .slice(0, this.abgp.batchReplicationSize) todo
      .map(v=> v.toPlainObject(publicKeys));

    return this.messageApi.packet(MessageTypes.DATA_REP, {
      data
    });
  }

  public dataResponse(packet: PacketModel) {
    const peerNode = this.abgp.nodes.get(packet.publicKey);
    const data: DbItem[] = packet.data.data
      .sort((a, b) =>
        (a.timestamp > b.timestamp ||
          (a.timestamp === b.timestamp && a.timestampIndex > b.timestampIndex)
        ) ? 1 : -1
      );

    for (const item of data) {
      this.abgp.remoteAppend(DbItem.fromPlainObject(item), peerNode);
    }
  }

}

export { NodeApi };
