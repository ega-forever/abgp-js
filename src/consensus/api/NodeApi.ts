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
    if (!this.abgp.nodes.has(packet.publicKey) || packet.dataUpdateTimestamp > Date.now()) {
      return null;
    }

    return packet;
  }

  public validateState(packet: PacketModel) {

    if (this.abgp.getStateRoot() === packet.root && this.abgp.nodes.get(packet.publicKey).dataUpdateTimestamp === packet.dataUpdateTimestamp) {
      this.abgp.emit(EventTypes.STATE_SYNCED, packet.publicKey);
      return null;
    }

    if (this.abgp.getStateRoot() === packet.root && this.abgp.nodes.get(packet.publicKey).dataUpdateTimestamp !== packet.dataUpdateTimestamp) {
      this.abgp.nodes.get(packet.publicKey).dataUpdateTimestamp = packet.dataUpdateTimestamp;

      if (this.abgp.dataUpdateTimestamp < packet.dataUpdateTimestamp) {
        this.abgp.dataUpdateTimestamp = packet.dataUpdateTimestamp;
      }

      this.abgp.emit(EventTypes.STATE_SYNCED, packet.publicKey);
      return null;
    }

    if (packet.dataUpdateTimestamp === this.abgp.nodes.get(packet.publicKey).dataUpdateTimestamp) {
      return null;
    }

    this.abgp.nodes.get(packet.publicKey).nextDataUpdateTimestamp = packet.dataUpdateTimestamp;
    return this.messageApi.packet(MessageTypes.STATE_REQ, {
      leave: packet.root
    });
  }

  public stateRequest(packet: PacketModel) {
    const layers = this.abgp.getLayers();
    return this.messageApi.packet(MessageTypes.STATE_REP, {
      layers
    });
  }

  public stateResponse(packet: PacketModel) {
    const layers = packet.data.layers[0];
    const localLayers = this.abgp.getLayers()[0];

    const unknownLayers = layers.filter((layer) => !localLayers.includes(layer));

    return this.messageApi.packet(MessageTypes.DATA_REQ, {
      layers: unknownLayers
    });
  }

  public dataRequest(packet: PacketModel) {
    const layers = packet.data.layers;
    const data: DbItem[] = [];

    for (const layer of layers) {
      if (!this.abgp.state.has(layer)) {
        continue;
      }
      const stateItem = this.abgp.state.get(layer);
      const dbHash = this.abgp.hashData(`${stateItem.key}:${stateItem.value}:${stateItem.version}`);
      const dbItem = this.abgp.db.get(`0x${dbHash}`);
      data.push(dbItem.toPlainObject([...this.abgp.publicKeys.keys()]) as any);
    }

    return this.messageApi.packet(MessageTypes.DATA_REP, {
      data
    });
  }

  public dataResponse(packet: PacketModel) {

    if (packet.dataUpdateTimestamp < this.abgp.nodes.get(packet.publicKey).nextDataUpdateTimestamp) {
      return null;
    }

    const data: DbItem[] = packet.data.data;

    for (const item of data) {
      this.abgp.remoteAppend(DbItem.fromPlainObject(item));
    }

    this.abgp.nodes.get(packet.publicKey).dataUpdateTimestamp = this.abgp.nodes.get(packet.publicKey).nextDataUpdateTimestamp;
    if (this.abgp.dataUpdateTimestamp < this.abgp.nodes.get(packet.publicKey).nextDataUpdateTimestamp) {
      this.abgp.dataUpdateTimestamp = this.abgp.nodes.get(packet.publicKey).nextDataUpdateTimestamp;
    }
  }

}

export { NodeApi };
