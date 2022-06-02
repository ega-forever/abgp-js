import { URL } from 'url';
// eslint-disable-next-line import/no-extraneous-dependencies
import { Client, Server } from 'jayson/promise';
import ABGP from '../../consensus/main';
import PacketModel from '../../consensus/models/PacketModel';

class TCPABGP extends ABGP {
  private server: Server;

  private clients: Map<string, Client> = new Map<string, Client>();

  public initialize() {
    this.logger.info(`initializing reply socket on port  ${this.address}`);

    this.server = new Server({
      rpc: async (args) => {
        const decoded = this.messageApi.decodePacket(Buffer.from(args[0], 'hex').toString());
        const reply = await this.requestProcessorService.process(decoded);
        return Buffer.from(JSON.stringify(reply)).toString('hex');
      }
    });

    const url = new URL(this.address);

    this.server.tcp().listen(parseInt(url.port, 10), url.hostname);
    this.logger.info(`server started on port: ${this.address}`);
  }

  /**
   * The message to write.
   *
   * @param {string} address The peer address
   * @param {Object} packet The packet to write to the connection.
   * @api private
   */
  public async call(address: string, packet: PacketModel): Promise<PacketModel> {
    if (!this.clients.has(address)) {
      const url = new URL(address);

      const client = Client.tcp({
        port: parseInt(url.port, 10),
        host: url.hostname
      });

      this.clients.set(address, client);
    }

    const response = await this.clients.get(address).request('rpc', [Buffer.from(JSON.stringify(packet)).toString('hex')]);

    if (response.error) {
      throw new Error(response.error);
    }

    return this.messageApi.decodePacket(Buffer.from(response.result, 'hex').toString());
  }

  public async disconnect(): Promise<void> {
    await super.disconnect();
    // @ts-ignore
    this.server.close();
  }

  public async connect(): Promise<void> {
    this.initialize();
    await super.connect();
  }
}

export default TCPABGP;
