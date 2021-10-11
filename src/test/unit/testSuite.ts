import Promise from 'bluebird';
import bunyan from 'bunyan';
import { expect } from 'chai';
import crypto from 'crypto';
import MessageTypes from '../../consensus/constants/MessageTypes';
import { ABGP } from '../../consensus/main';
import { PacketModel } from '../../consensus/models/PacketModel';
import { generateRandomRecords, getUniqueRoots, getUniqueTimestamps, syncNodesBetweenEachOther } from '../utils/helpers';

export function testSuite(ctx: any = {}, nodesCount: number) {

  beforeEach(async () => {

    ctx.keys = [];

    ctx.nodes = [];

    for (let i = 0; i < nodesCount; i++) {
      const node = crypto.createECDH('secp256k1');
      node.generateKeys();
      ctx.keys.push({
        privateKey: node.getPrivateKey().toString('hex'),
        publicKey: node.getPublicKey('hex', 'compressed')
      });
    }

    for (let index = 0; index < nodesCount; index++) {
      const instance = new ABGP({
        address: ctx.keys[index].publicKey,
        gossipInterval: {
          min: 500,
          max: 1000
        },
        sendSignalToRandomPeer: false,
        logger: bunyan.createLogger({ name: 'abgp.logger', level: 60 }),
        privateKey: ctx.keys[index].privateKey
      });

      for (let i = 0; i < nodesCount; i++)
        if (i !== index)
          instance.nodeApi.join(ctx.keys[i].publicKey);

      ctx.nodes.push(instance);
    }

  });

  it(`should sync state`, async () => {

    const nodesWithRecords: ABGP[] = ctx.nodes.slice(0, 2);

    for (const node of nodesWithRecords) {
      generateRandomRecords(node);
    }

    for (let i = 0; i < ctx.nodes.length; i++) {
      for (let s = 0; s < ctx.nodes.length; s++) {
        if (i === s) {
          continue;
        }

        const node1: ABGP = ctx.nodes[i];
        const node2: ABGP = ctx.nodes[s];

        const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);
        // @ts-ignore
        const node2ValidateState: PacketModel = await node2.requestProcessorService.process(node1PacketAck);
        expect(node2ValidateState.type).to.eq(MessageTypes.STATE_REQ);

        // @ts-ignore
        const node1StateRequest: PacketModel = await node1.requestProcessorService.process(node2ValidateState);
        expect(node1StateRequest.type).to.eq(MessageTypes.STATE_REP);

        // @ts-ignore
        const node2StateResponse: PacketModel = await node2.requestProcessorService.process(node1StateRequest);

        // @ts-ignore
        const node1DataRequest: PacketModel = await node1.requestProcessorService.process(node2StateResponse);

        // @ts-ignore
        await node2.requestProcessorService.process(node1DataRequest);

        // @ts-ignore
        const node2ValidateStateAfterApply = await node2.requestProcessorService.process(node1PacketAck);

        expect(node2ValidateStateAfterApply).to.eq(null);
      }
    }

    await syncNodesBetweenEachOther(ctx.nodes);

    const rootReduces = getUniqueRoots(ctx.nodes);
    expect(rootReduces.length).to.eq(1);

    const timestampReduces = getUniqueTimestamps(ctx.nodes);
    expect(timestampReduces.length).to.eq(1);
  });

  it(`should sync after drop (f, in N = 2f + 1)`, async () => {

    const majority = Math.ceil(ctx.nodes.length / 2) + 1;
    const nodesMajority: ABGP[] = ctx.nodes.slice(0, majority);
    const nodesMinor: ABGP[] = ctx.nodes.slice(majority);

    for (const node of nodesMajority) {
      generateRandomRecords(node);
    }

    for (let i = 0; i < ctx.nodes.length; i++) {
      for (let s = 0; s < ctx.nodes.length; s++) {
        if (i === s) {
          continue;
        }

        const node1: ABGP = ctx.nodes[i];
        const node2: ABGP = ctx.nodes[s];

        const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);
        // @ts-ignore
        const node2ValidateState: PacketModel = await node2.requestProcessorService.process(node1PacketAck);
        if (!node2ValidateState) {
          continue;
        }
        // @ts-ignore
        const node1StateRequest: PacketModel = await node1.requestProcessorService.process(node2ValidateState);
        // @ts-ignore
        const node2StateResponse: PacketModel = await node2.requestProcessorService.process(node1StateRequest);
        // @ts-ignore
        const node1DataRequest: PacketModel = await node1.requestProcessorService.process(node2StateResponse);
        // @ts-ignore
        await node2.requestProcessorService.process(node1DataRequest);

        // @ts-ignore
        const node2ValidateStateAfterApply = await node2.requestProcessorService.process(node1PacketAck);
        expect(node2ValidateStateAfterApply).to.eq(null);
      }
    }

    await syncNodesBetweenEachOther(ctx.nodes);

    for (const node of nodesMinor) {
      node.dataUpdateTimestamp = 0;
      node.nextDataUpdateTimestamp = 0;

      for (const key of node.state.keys()) {
        node.state.delete(key);
      }

      for (const key of node.db.keys()) {
        node.db.delete(key);
      }

      for (const peerNode of node.nodes.values()) {
        peerNode.dataUpdateTimestamp = 0;
        peerNode.nextDataUpdateTimestamp = 0;
      }

      node.rebuildTree();
    }

    await syncNodesBetweenEachOther(ctx.nodes);

    const rootReduces = getUniqueRoots(ctx.nodes);
    expect(rootReduces.length).to.eq(1);

    const timestampReduces = getUniqueTimestamps(ctx.nodes);
    expect(timestampReduces.length).to.eq(1);
  });

  it(`should fail to sync fake state with fake private and public keys (f, in N = 2f + 1)`, async () => {

    const majority = Math.floor(ctx.nodes.length / 2) + 1;
    const nodesMajority: ABGP[] = ctx.nodes.slice(0, majority);
    const nodesFail: ABGP[] = ctx.nodes.slice(majority);

    for (const node of nodesMajority) {
      generateRandomRecords(node);
    }

    for (const node of nodesFail) {
      const c = crypto.createECDH('secp256k1');
      c.generateKeys();

      // @ts-ignore
      node.privateKey = c.getPrivateKey().toString('hex');

      // @ts-ignore
      node.publicKey = c.getPublicKey('hex', 'compressed');

      generateRandomRecords(node);
    }

    await syncNodesBetweenEachOther(ctx.nodes);

    const rootReduces = getUniqueRoots(ctx.nodes);
    expect(rootReduces.length).to.eq(nodesFail.length + 1);
  });

  it(`should fail to sync fake state with fake private key and real public key (f, in N = 2f + 1)`, async () => {

    const majority = Math.floor(ctx.nodes.length / 2) + 1;
    const nodesMajority: ABGP[] = ctx.nodes.slice(0, majority);
    const nodesFail: ABGP[] = ctx.nodes.slice(majority);

    for (const node of nodesMajority) {
      generateRandomRecords(node);
    }

    for (const node of nodesFail) {
      const c = crypto.createECDH('secp256k1');
      c.generateKeys();

      // @ts-ignore
      node.privateKey = c.getPrivateKey().toString('hex');

      generateRandomRecords(node);
    }

    await syncNodesBetweenEachOther(ctx.nodes);

    const rootReduces = getUniqueRoots(ctx.nodes);
    expect(rootReduces.length).to.eq(nodesFail.length + 1);
  });

  it(`should sync when there were updates between state_req and data_req`, async() => {

    const unsyncedNode: ABGP = ctx.nodes[0];
    const updatedNode: ABGP = ctx.nodes[1];
    const restNodes: ABGP[] = ctx.nodes.slice(2);

    for (const node of [updatedNode, ...restNodes]) {
      generateRandomRecords(node);
    }

    const updatedNodePacketAck = updatedNode.messageApi.packet(MessageTypes.ACK);
    // @ts-ignore
    const unsyncedNodeValidateState: PacketModel = await unsyncedNode.requestProcessorService.process(updatedNodePacketAck);
    // @ts-ignore
    const updatedNodeStateRequest: PacketModel = await updatedNode.requestProcessorService.process(unsyncedNodeValidateState);
    // @ts-ignore
    const unsyncedNodeStateResponse: PacketModel = await unsyncedNode.requestProcessorService.process(updatedNodeStateRequest);

    generateRandomRecords(updatedNode);

    // @ts-ignore
    const updatedNodeDataRequest: PacketModel = await updatedNode.requestProcessorService.process(unsyncedNodeStateResponse);
    // @ts-ignore
    await unsyncedNode.requestProcessorService.process(updatedNodeDataRequest);

    const updatedNodePacketAckAfterApply = updatedNode.messageApi.packet(MessageTypes.ACK);
    // @ts-ignore
    const unsyncedNodeValidateStateAfterApply: PacketModel = await unsyncedNode.requestProcessorService.process(updatedNodePacketAckAfterApply);
    expect(unsyncedNodeValidateStateAfterApply.type).to.eq(MessageTypes.STATE_REQ);

    await syncNodesBetweenEachOther(ctx.nodes);

    const rootReduces = getUniqueRoots(ctx.nodes);
    expect(rootReduces.length).to.eq(1);

    const timestampReduces = getUniqueTimestamps(ctx.nodes);
    expect(timestampReduces.length).to.eq(1);
  });

  afterEach(async () => {
    await Promise.delay(1000);
  });

}
