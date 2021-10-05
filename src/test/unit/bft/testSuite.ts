import Promise from 'bluebird';
import bunyan from 'bunyan';
import { expect } from 'chai';
import crypto from 'crypto';
import MessageTypes from '../../../consensus/constants/MessageTypes';
import messageTypes from '../../../consensus/constants/MessageTypes';
import * as utils from '../../../consensus/utils/cryptoUtils';
import { BGP } from '../../../consensus/main';

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
      const instance = new BGP({
        address: ctx.keys[index].publicKey,
        gossipInterval: {
          min: 500,
          max: 1000
        },
        sendSignalToRandomPeer: false,
        logger: bunyan.createLogger({ name: 'mokka.logger', level: 60 }),
        privateKey: ctx.keys[index].privateKey
      });

      for (let i = 0; i < nodesCount; i++)
        if (i !== index)
          instance.nodeApi.join(ctx.keys[i].publicKey);

      ctx.nodes.push(instance);
    }

  });

  it(`should sync state`, async () => {

    const nodesWithRecords: BGP[] = ctx.nodes.slice(0, 2);
    const nodesWithoutRecords: BGP[] = ctx.nodes.slice(2);

    for (const node of nodesWithRecords) {
      const randomNumber = 7 + Math.ceil((15 - 7) * Math.random());

      for (let i = 0; i < randomNumber; i++) {
        const record = {
          key: Math.random().toString(16).substr(2) + i,
          value: Math.random().toString(16).substr(2) + i,
          version: 1
        }
        node.append(record.key, record.key, record.version);
      }
    }


    for (let i = 0; i < ctx.nodes.length; i++) {
      for (let s = 0; s < ctx.nodes.length; s++) {
        if(i === s){
          continue;
        }

        const node1: BGP = ctx.nodes[i];
        const node2: BGP = ctx.nodes[s];

        const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);
        const node2ValidateState = node2.nodeApi.validateState(node1PacketAck);
        expect(node2ValidateState.type).to.eq(MessageTypes.STATE_REQ);

        const node1StateRequest = node1.nodeApi.stateRequest(node2ValidateState);
        expect(node1StateRequest.type).to.eq(MessageTypes.STATE_REP);
        const node2StateResponse = node2.nodeApi.stateResponse(node1StateRequest);

        const node1DataRequest = node1.nodeApi.dataRequest(node2StateResponse);
        node2.nodeApi.dataResponse(node1DataRequest);

        const node2ValidateStateAfterApply = node2.nodeApi.validateState(node1PacketAck);
        console.log(node2ValidateStateAfterApply)

      }
    }

    for (let i = 0; i < ctx.nodes.length; i++) {
      for (let s = 0; s < ctx.nodes.length; s++) {
        if(i === s){
          continue;
        }

        const node1: BGP = ctx.nodes[i];
        const node2: BGP = ctx.nodes[s];

        const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);
        const node2ValidateState = node2.nodeApi.validateState(node1PacketAck);

        console.log(node1PacketAck.root, node1PacketAck.vectorClock, '/', node2ValidateState.root, node2ValidateState.vectorClock);
        console.log(node1.state.size, node2.state.size)

        // expect(node2ValidateState).to.undefined;

     /*   const node1StateRequest = node1.nodeApi.stateRequest(node2ValidateState);
        expect(node1StateRequest.type).to.eq(MessageTypes.STATE_REP);
        const node2StateResponse = node2.nodeApi.stateResponse(node1StateRequest);

        const node1DataRequest = node1.nodeApi.dataRequest(node2StateResponse);
        node2.nodeApi.dataResponse(node1DataRequest);

        const node2ValidateStateAfterApply = node2.nodeApi.validateState(node1PacketAck);
        console.log(node2ValidateStateAfterApply)*/

      }
    }

  /*  const node1: BGP = ctx.nodes[0];
    const node2: BGP = ctx.nodes[1];

    const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);
    const node2ValidateState = node2.nodeApi.validateState(node1PacketAck);
    expect(node2ValidateState.type).to.eq(MessageTypes.STATE_REQ);

    const node1StateRequest = node1.nodeApi.stateRequest(node2ValidateState);
    expect(node1StateRequest.type).to.eq(MessageTypes.STATE_REP);

    const node2StateResponse = node2.nodeApi.stateResponse(node1StateRequest);

    const node1DataRequest = node1.nodeApi.dataRequest(node2StateResponse);

    node2.nodeApi.dataResponse(node1DataRequest);

    console.log(node2.state.size)

    const node2ValidateStateAfterApply = node2.nodeApi.validateState(node1PacketAck);
    console.log(node2ValidateStateAfterApply)
*/

  });


  afterEach(async () => {
    await Promise.delay(1000);
  });

}
