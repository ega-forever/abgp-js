import { MessageApi } from './api/MessageApi';
import { NodeApi } from './api/NodeApi';
import { GossipController } from './controllers/GossipController';
import { ILoggerInterface } from './interfaces/ILoggerInterface';
import { ISettingsInterface } from './interfaces/ISettingsInterface';
import { NodeModel } from './models/NodeModel';
import { PacketModel } from './models/PacketModel';
import { RequestProcessorService } from './services/RequestProcessorService';

class ABGP extends NodeModel {

  public readonly nodeApi: NodeApi;
  public readonly messageApi: MessageApi;
  public readonly gossipCtrl: GossipController;
  public readonly reqMiddleware: (packet: PacketModel) => Promise<PacketModel>;
  public readonly resMiddleware: (packet: PacketModel, peerPublicKey: string) => Promise<PacketModel>;
  public readonly logger: ILoggerInterface;
  private readonly requestProcessorService: RequestProcessorService;

  constructor(options: ISettingsInterface) {
    super(options.privateKey, options.address);

    this.gossipInterval = options.gossipInterval;
    this.sendSignalToRandomPeer = options.sendSignalToRandomPeer;
    this.logger = options.logger || {
      // tslint:disable-next-line
      error: console.log,
      // tslint:disable-next-line
      info: console.log,
      // tslint:disable-next-line
      trace: console.log
    };

    this.reqMiddleware = options.reqMiddleware ? options.reqMiddleware :
      async (packet: PacketModel) => packet;

    this.resMiddleware = options.resMiddleware ? options.resMiddleware :
      async (packet: PacketModel) => packet;

    this.gossipCtrl = new GossipController(this);
    this.requestProcessorService = new RequestProcessorService(this);
    this.nodeApi = new NodeApi(this);
    this.messageApi = new MessageApi(this);
    if (options.publicKeys) {
      for (const publicKey of options.publicKeys) {
        this.publicKeys.add(publicKey);
      }
    }
    this.publicKeys.add(this.publicKey);
  }

  public quorum(responses: number) { //todo maybe remove?
    if (!this.nodes.size || !responses) return false;

    return responses >= this.majority();
  }

  public connect(): void {
    this.gossipCtrl.watchBeat();
  }

  public async disconnect(): Promise<void> {
    await this.gossipCtrl.stopBeat();
  }

  public async emitPacket(packet: Buffer) {
    let parsedPacket = this.messageApi.decodePacket(packet);
    parsedPacket = await this.reqMiddleware(parsedPacket);
    const reply = await this.requestProcessorService.process(parsedPacket);
    if (reply) {
      await this.messageApi.message(reply, parsedPacket.publicKey);
    }
  }

}

export { ABGP };
