// eslint-disable-next-line import/no-extraneous-dependencies
import * as bunyan from 'bunyan';
import eventTypes from '../../../consensus/constants/EventTypes';
import RPCABGP from '../../../implementation/node/RPC';
import PlainStorage from '../../../implementation/storage/PlainStorage';

let instance: RPCABGP = null;

const init = (params: any) => {
  const logger = bunyan.createLogger({ name: `abgp.logger[${params.index}]`, level: 50 });

  logger.trace(`params ${JSON.stringify(params)}`);

  const indexNodesLinks: number[] = params.links || params.keys.map((s, i) => i);
  const allPublicKeys: string[] = params.keys.map((key) => key.publicKey);

  instance = new RPCABGP({
    address: `http://127.0.0.1:${2000 + params.index}/${params.publicKey || params.keys[params.index].publicKey}`,
    gossipInterval: {
      min: params.settings.gossipInterval.min,
      max: params.settings.gossipInterval.max
    },
    sendSignalToRandomPeer: params.sendSignalToRandomPeer,
    logger,
    privateKey: params.keys[params.index].privateKey,
    publicKeys: allPublicKeys,
    storage: new PlainStorage()
  });

  for (const index of indexNodesLinks) {
    if (index !== params.index) {
      instance.nodeApi.join(`http://127.0.0.1:${2000 + index}/${params.keys[index].publicKey}`);
    }
  }

  instance.on(eventTypes.STATE_SYNCED, () => {
    logger.info(`index #${params.index} root ${instance.getStateRoot()} / lastTimestamp: ${instance.lastUpdateTimestamp}`);
    process.send({
      type: 'state_synced',
      args: [instance.getStateRoot(), instance.lastUpdateTimestamp]
    });
  });
};

process.on('message', (m: any) => {
  if (m.type === 'init') {
    init(m.args[0]);
  }

  if (m.type === 'connect') {
    instance.connect();
  }

  if (m.type === 'append') {
    instance.appendApi.append(m.args[0], m.args[1], m.args[2]);
  }
});
