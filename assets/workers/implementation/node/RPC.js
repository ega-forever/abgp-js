"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
/* eslint-disable import/no-extraneous-dependencies */
const axios_1 = __importDefault(require("axios"));
const body_parser_1 = __importDefault(require("body-parser"));
const express_1 = __importDefault(require("express"));
const url_1 = require("url");
const main_1 = __importDefault(require("../../consensus/main"));
class RPCABGP extends main_1.default {
    constructor() {
        super(...arguments);
        this.app = (0, express_1.default)();
    }
    initialize() {
        this.app.use(body_parser_1.default.json());
        this.app.post('/', async (req, res) => {
            const packet = Buffer.from(req.body.data, 'hex');
            const decoded = this.messageApi.decodePacket(packet.toString());
            // eslint-disable-next-line @typescript-eslint/no-floating-promises
            const reply = await this.requestProcessorService.process(decoded);
            res.send(Buffer.from(JSON.stringify(reply)).toString('hex'));
        });
        const url = new url_1.URL(this.address);
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
    async call(address, packet) {
        const reply = await axios_1.default.post(address, {
            data: Buffer.from(JSON.stringify(packet)).toString('hex')
        }, {
            timeout: this.gossipInterval.max
        });
        return this.messageApi.decodePacket(Buffer.from(reply.data, 'hex').toString());
    }
    async disconnect() {
        await super.disconnect();
        this.app.close();
    }
    async connect() {
        this.initialize();
        await super.connect();
    }
}
exports.default = RPCABGP;
//# sourceMappingURL=RPC.js.map