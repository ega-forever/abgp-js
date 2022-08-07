const window = self;
const path = window.location.pathname.split(/(\/*.{0,}\/workers\/)/gm, 2).find(el => el.length);
importScripts(`${path}bundle.js`);
importScripts(`${path}implementation/crypto/bundle.js`);
importScripts(`${path}implementation/storage/bundle.js`);


const requests = new Map();

class BrowserABGP extends ABGP.default {

  initialize() {
  }

  async call(address, packet) {
    const id = `${address} - ${Date.now()}`;
    self.postMessage({type: 'packet', args: [address, JSON.stringify(packet)], id});
    return new Promise(res => {
      requests.set(id, res);
    });
  }

  connect() {
    this.initialize();
    super.connect();
  }

}

const init = (index, keys, settings) => {

  window.abgp = new BrowserABGP({
    address: `${index}/${keys[index].publicKey}`,
    gossipInterval: {
      min: settings.gossipInterval.min,
      max: settings.gossipInterval.max
    },
    logger: {
      info: (text) => console.log(`worker#${index} ${text}`),
      error: (text) => console.log(`worker#${index} ${text}`),
      warn: (text) => console.log(`worker#${index} ${text}`),
      trace: (text) => {}
    },
    privateKey: keys[index].privateKey,
    storage: new PlainStorage(),
    crypto: new PlainCrypto()
  });

  for (let i = 0; i < keys.length; i++)
    if (i !== index)
      window.abgp.nodeApi.join(`${i}/${keys[i].publicKey}`);

  window.abgp.connect();

  window.abgp.on('STATE_UPDATE', async () => {
    const state = await window.abgp.getState();
    window.abgp.logger.info(`state: ${state.root}`);
    self.postMessage({
      type: 'info',
      args: [{stateRoot: state.root, lastUpdateTimestamp: state.timestamp}]
    });
  });

};

self.addEventListener('message', async function (e) {

  if (!e.data) {
    return;
  }

  if (e.data.type === 'init') {
    return init(...e.data.args);
  }

  if (e.data.type === 'packet') {
    const packet = JSON.parse(e.data.args[0]);

    if (requests.has(e.data.id)) {
      requests.get(e.data.id)(packet);
      requests.delete(e.data.id);
    } else {
      const reply = await window.abgp.requestProcessorService.process(packet);
      const node = window.abgp.nodes.get(packet.publicKey);
      self.postMessage({type: 'packet', args: [node.address, JSON.stringify(reply)], id: e.data.id});
    }
  }

  if (e.data.type === 'add_record') {
    await window.abgp.appendApi.append(...e.data.args);
  }

  if (e.data.type === 'get_records') {
    const records = [...window.abgp.storage.Record.db.values()].map((v) => ({
      key: v.key,
      value: v.value,
      signaturesMap: Object.fromEntries(v.signaturesMap),
      timestamp: v.timestamp,
      publicKeys: Array.from(v.publicKeys),
      signatureType: v.signatureType
    }));

    self.postMessage({
      type: 'records',
      args: [records]
    });
  }


}, false);
