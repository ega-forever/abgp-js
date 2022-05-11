import MessageApi from '../api/MessageApi';
import NodeApi from '../api/NodeApi';
import messageTypes from '../constants/MessageTypes';
import ABGP from '../main';

export default class GossipController {
  private abgp: ABGP;

  private readonly messageApi: MessageApi;

  private readonly nodeApi: NodeApi;

  private runBeat: boolean;

  constructor(abgp: ABGP) {
    this.abgp = abgp;
    this.messageApi = new MessageApi(abgp);
    this.nodeApi = new NodeApi(abgp);
    this.runBeat = false;
  }

  public async stopBeat() {
    this.runBeat = false;
  }

  public async watchBeat() {
    this.runBeat = true;

    while (this.runBeat) {
      const nodes = [];

      if (this.abgp.sendSignalToRandomPeer) {
        const nodesAmount = this.abgp.nodes.size;
        const randomNode = [...this.abgp.nodes.values()][Math.round(Math.random() * (nodesAmount - 1))];
        nodes.push(randomNode);
      } else {
        nodes.push(...this.abgp.nodes.values());
      }

      await Promise.all(
        nodes.map(async (node) => {
          const packet = await this.messageApi.packet(messageTypes.ACK);
          this.abgp.logger.trace(`sending ack signal to peer (${node.publicKey})`);
          return this.messageApi.message(packet, node.publicKey);
        })
      );

      this.abgp.logger.trace(`sent ack signal to peers (${nodes.length})`);
      const interval = Math.random() * (this.abgp.gossipInterval.max - this.abgp.gossipInterval.min) + this.abgp.gossipInterval.min;
      await new Promise((res) => setTimeout(res, interval));

      while (this.abgp.requestProcessorService.isDataResponseSemaphoreProcess()) {
        this.abgp.logger.trace(`awaiting for append queue to draw (left ${this.abgp.requestProcessorService.leftDataResponseSemaphoreProcessQueue()})`);
        await new Promise((res) => setTimeout(res, interval));
      }
    }
  }
}
