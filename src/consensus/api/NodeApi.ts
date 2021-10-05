import eventTypes from '../constants/EventTypes';
import { BGP } from '../main';
import { NodeModel, StateItem } from '../models/NodeModel';
import { PacketModel } from '../models/PacketModel';
import { MessageApi } from './MessageApi';
import MessageTypes from '../constants/MessageTypes';

class NodeApi {

  private readonly bgp: BGP;
  private messageApi: MessageApi;

  constructor(bgp: BGP) {
    this.bgp = bgp;
    this.messageApi = new MessageApi(bgp);
  }

  public join(multiaddr: string): NodeModel {

    const publicKey = multiaddr.match(/\w+$/).toString();

    if (this.bgp.publicKey === publicKey)
      return;

    const node = new NodeModel(null, multiaddr);

    node.write = this.bgp.write.bind(this.bgp);
    node.once('end', () => this.leave(node.publicKey));

    this.bgp.nodes.set(publicKey, node);

    // this.buildPublicKeysRootAndCombinations();
    this.bgp.emit(eventTypes.NODE_JOIN, node);
    return node;
  }

  /*  public buildPublicKeysRootAndCombinations() {//todo maybe need to return
      const sortedPublicKeys = [...this.bgp.nodes.keys(), this.bgp.publicKey].sort();
      this.bgp.publicKeysRoot = utils.buildPublicKeysRoot(sortedPublicKeys);
      this.bgp.publicKeysCombinationsInQuorum = getCombinations(sortedPublicKeys, this.bgp.majority());
    }*/

  public leave(publicKey: string): void {

    const node = this.bgp.nodes.get(publicKey);
    this.bgp.nodes.delete(publicKey);

    // this.buildPublicKeysRootAndCombinations();
    this.bgp.emit(eventTypes.NODE_LEAVE, node);
  }

  public validateState(packet: PacketModel) {
    if (this.bgp.getStateRoot() === packet.root || packet.vectorClock === this.bgp.nodes.get(packet.publicKey).vectorClock) { //todo compare with vector clock of local copy of node
      return;
    }

    return this.messageApi.packet(MessageTypes.STATE_REQ, {
      leave: packet.root
    });
  }

  public stateRequest(packet: PacketModel) {
    const layers = this.bgp.getLayers();
    return this.messageApi.packet(MessageTypes.STATE_REP, {
      layers
    });
  }

  public stateResponse(packet: PacketModel) {
    const layers = packet.data.layers[0];
    const localLayers = this.bgp.getLayers()[0];

    const unknownLayers = layers.filter(layer => !localLayers.includes(layer));

    return this.messageApi.packet(MessageTypes.DATA_REQ, {
      layers: unknownLayers
    });
  }

  public dataRequest(packet: PacketModel) {
    const layers = packet.data.layers;
    const data:  = [];

    for (const layer of layers) {
      if (!this.bgp.state.has(layer)) {
        continue;
      }
      const item = this.bgp.state.get(layer);
      data.push(item);
    }

    return this.messageApi.packet(MessageTypes.STATE_REP, {
      data
    });
  }

  public dataResponse(packet: PacketModel) {
    const data: StateItem[] = packet.data.data;

    for (const item of data) {
      this.bgp.append(item.key, item.value, item.version);
    }

    this.bgp.nodes.get(packet.publicKey).vectorClock = packet.vectorClock;
    if (this.bgp.vectorClock < packet.vectorClock) {
      this.bgp.vectorClock = packet.vectorClock;
    }
  }

}

export { NodeApi };
