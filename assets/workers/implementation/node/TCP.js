"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const url_1 = require("url");
// eslint-disable-next-line import/no-extraneous-dependencies
const promise_1 = require("jayson/promise");
const main_1 = __importDefault(require("../../consensus/main"));
class TCPABGP extends main_1.default {
    constructor() {
        super(...arguments);
        this.clients = new Map();
    }
    initialize() {
        this.logger.info(`initializing reply socket on port  ${this.address}`);
        this.server = new promise_1.Server({
            rpc: async (args) => {
                const decoded = this.messageApi.decodePacket(Buffer.from(args[0], 'hex').toString());
                const reply = await this.requestProcessorService.process(decoded);
                return Buffer.from(JSON.stringify(reply)).toString('hex');
            }
        });
        const url = new url_1.URL(this.address);
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
    async call(address, packet) {
        if (!this.clients.has(address)) {
            const url = new url_1.URL(address);
            const client = promise_1.Client.tcp({
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
    async disconnect() {
        await super.disconnect();
        // @ts-ignore
        this.server.close();
    }
    async connect() {
        this.initialize();
        await super.connect();
    }
}
exports.default = TCPABGP;
//# sourceMappingURL=TCP.js.map