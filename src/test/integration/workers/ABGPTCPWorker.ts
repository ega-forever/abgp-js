import * as bunyan from 'bunyan';
import eventTypes from '../../../consensus/constants/EventTypes';
import TCPABGP from '../../../implementation/TCP';

let instance: TCPABGP = null;

const init = (params: any) => {

  const logger = bunyan.createLogger({ name: `abgp.logger[${params.index}]`, level: 50 });

  logger.trace(`params ${JSON.stringify(params)}`);

  const indexNodesLinks: number[] = params.links || params.keys.map((s, i) => i);
  const allPublicKeys: string[] = params.keys.map(key=> key.publicKey);

  instance = new TCPABGP({
    address: `tcp://127.0.0.1:${8000 + params.index}/${params.publicKey || params.keys[params.index].publicKey}`,
    gossipInterval: {
      min: params.settings.gossipInterval.min,
      max: params.settings.gossipInterval.max
    },
    sendSignalToRandomPeer: params.sendSignalToRandomPeer,
    logger,
    privateKey: params.keys[params.index].privateKey,
    publicKeys: allPublicKeys
  });

  for (const index of indexNodesLinks) {
    if (index !== params.index) {
      instance.nodeApi.join(`tcp://127.0.0.1:${8000 + index}/${params.keys[index].publicKey}`);
    }
  }

  instance.on(eventTypes.STATE_SYNCED, () => {
    logger.info(`index #${params.index} root ${instance.getStateRoot()} / stateItems: ${instance.state.size} / dbSize: ${instance.db.size} / lastTimestamp: ${instance.dataUpdateTimestamp}`);
    process.send({
      type: 'state_synced',
      args: [instance.getStateRoot(), instance.dataUpdateTimestamp, instance.db.size]
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
    instance.append(m.args[0], m.args[1], m.args[2]);
  }
});
