/* eslint-disable import/no-extraneous-dependencies */
import axios from 'axios';
import bodyParser from 'body-parser';
import express from 'express';
import { URL } from 'url';
import ABGP from 'abgp-js';
import PacketModel from 'abgp-js/dist/consensus/models/PacketModel';

class RPCABGP extends ABGP {
  private app = express();

  public initialize() {
    this.app.use(bodyParser.json());

    this.app.post('/', async (req, res) => {
      const packet = Buffer.from(req.body.data, 'hex');
      const decoded = this.messageApi.decodePacket(packet.toString());
      // eslint-disable-next-line @typescript-eslint/no-floating-promises
      const reply = await this.requestProcessorService.process(decoded);
      res.send(Buffer.from(JSON.stringify(reply)).toString('hex'));
    });

    const url = new URL(this.address);

    this.app.listen(url.port, () => {
      this.logger.info(`rpc started on port ${url.port}`);
    });
  }

  /**
   * The message to write.
   *
   * @param {string} address The peer address
   * @param {Object} packet The packet to write to the connection.
   * @api private
   */
  public async call(address: string, packet: PacketModel): Promise<PacketModel> {
    const reply = await axios.post(address, {
      data: Buffer.from(JSON.stringify(packet)).toString('hex')
    }, {
      timeout: this.gossipInterval.max
    });

    return this.messageApi.decodePacket(Buffer.from(reply.data, 'hex').toString());
  }

  public async disconnect(): Promise<void> {
    await super.disconnect();
    this.app.close();
  }

  public async connect(): Promise<void> {
    this.initialize();
    await super.connect();
  }
}

export default RPCABGP;
