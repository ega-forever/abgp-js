import ABGP from '../../consensus/main';
import PacketModel from '../../consensus/models/PacketModel';
declare class RPCABGP extends ABGP {
    private app;
    initialize(): void;
    /**
     * The message to write.
     *
     * @param {string} address The peer address
     * @param {Object} packet The packet to write to the connection.
     * @api private
     */
    call(address: string, packet: PacketModel): Promise<PacketModel>;
    disconnect(): Promise<void>;
    connect(): Promise<void>;
}
export default RPCABGP;
