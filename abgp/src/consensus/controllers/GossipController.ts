import MessageApi from '../api/MessageApi';
import NodeApi from '../api/NodeApi';
import messageTypes from '../constants/MessageTypes';
import ABGP from '../main';
import RecordModel from '../models/RecordModel';
import NodeModel from '../models/NodeModel';
import EventTypes from '../constants/EventTypes';
import PacketModel from '../models/PacketModel';

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
      const sortedPublicKeys = [...this.abgp.publicKeys.keys()].sort();

      if (this.abgp.sendSignalToRandomPeer) {
        const nodesAmount = this.abgp.nodes.size;
        const randomNode = [...this.abgp.nodes.values()][Math.round(Math.random() * (nodesAmount - 1))];
        nodes.push(randomNode);
      } else {
        nodes.push(...this.abgp.nodes.values());
      }

      const replies = await Promise.all(
        nodes.map(async (node: NodeModel) => {
          const peerNodeState = await node.getState();

          const packet = await this.messageApi.packet(messageTypes.DATA_REQ, {
            lastUpdateTimestamp: peerNodeState.timestamp,
            lastUpdateTimestampIndex: peerNodeState.timestampIndex
          });

          let replyPacket: PacketModel;

          try {
            replyPacket = await this.abgp.messageApi.message(packet, node.publicKey);
          } catch (e) {
            this.abgp.logger.warn(`error peer (${nodes.length}) not available: ${e.toString()}`);
            return {
              node,
              root: '0',
              data: []
            };
          }

          if (
            peerNodeState.root === replyPacket.root &&
            peerNodeState.timestamp === replyPacket.lastUpdateTimestamp &&
            peerNodeState.timestampIndex === replyPacket.lastUpdateTimestampIndex) {
            this.abgp.emit(EventTypes.STATE_SYNCED, replyPacket.publicKey);
            return {
              node,
              root: '0',
              data: []
            };
          }

          if (!replyPacket.data) {
            this.abgp.logger.trace(`error packet from peer (${nodes.length}) with type ${replyPacket.type}`);
            return {
              node,
              root: '0',
              data: []
            };
          }

          const data = replyPacket.data.data
            .sort((a, b) =>
              ((a.timestamp > b.timestamp ||
                (a.timestamp === b.timestamp && a.timestampIndex > b.timestampIndex)
              ) ? 1 : -1));

          return {
            node,
            data,
            root: replyPacket.root
          };
        })
      );

      for (const reply of replies) {
        for (const item of reply.data) {
          await this.abgp.appendApi.remoteAppend(
            RecordModel.fromPlainObject(item, sortedPublicKeys),
            reply.node,
            reply.root
          );
        }
      }

      this.abgp.logger.trace(`sent ack signal to peers (${nodes.length})`);
      const interval = Math.random() * (this.abgp.gossipInterval.max - this.abgp.gossipInterval.min) + this.abgp.gossipInterval.min;
      await new Promise((res) => setTimeout(res, interval));
    }
  }
}
