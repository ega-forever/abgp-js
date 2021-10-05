import { MessageApi } from '../api/MessageApi';
import { NodeApi } from '../api/NodeApi';
import messageTypes from '../constants/MessageTypes';
import { BGP } from '../main';

class GossipController {

  private bgp: BGP;
  private messageApi: MessageApi;
  private nodeApi: NodeApi;
  private runBeat: boolean;

  constructor(bgp: BGP) {
    this.bgp = bgp;
    this.messageApi = new MessageApi(bgp);
    this.nodeApi = new NodeApi(bgp);
    this.runBeat = false;
  }

  public async stopBeat() {
    this.runBeat = false;
  }

  public async watchBeat() {

    this.runBeat = true;

    while (this.runBeat) {
      this.bgp.logger.trace(`sending state signal to peers`);

      const nodes = [];

      if (this.bgp.sendSignalToRandomPeer) {
        const nodesAmount = this.bgp.nodes.size;
        const randomNode = [...this.bgp.nodes.values()][Math.random() * nodesAmount - 1];
        nodes.push(randomNode);
      } else {
        nodes.push(...this.bgp.nodes.values());
      }

      await Promise.all(
        nodes.map((node) => {
          const packet = this.messageApi.packet(messageTypes.ACK); //todo reconsider packet types
          return this.messageApi.message(packet, node.publicKey);
        }));

      this.bgp.logger.trace(`sent ack signal to peers`);
      const interval = Math.random() * (this.bgp.gossipInterval.max - this.bgp.gossipInterval.min) + this.bgp.gossipInterval.min;
      await new Promise(res => setTimeout(res, interval));
    }

  }
}

export { GossipController };
