const window = self;
const path = window.location.pathname.split(/(\/*.{0,}\/workers\/)/gm, 2).find(el => el.length);
importScripts(`${path}bundle.js`);

class BrowserABGP extends ABGP.default {

  initialize() {
  }

  async write(address, packet) {
    self.postMessage({type: 'packet', args: [address, packet], id: Date.now()});
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
      // trace: (text) => console.log(`worker#${index} ${text}`)
      trace: (text) => {
      }
    },
    privateKey: keys[index].privateKey
  });

  for (let i = 0; i < keys.length; i++)
    if (i !== index)
      window.abgp.nodeApi.join(`${i}/${keys[i].publicKey}`);

  window.abgp.connect();

  window.abgp.on('STATE_UPDATE', () => {
    window.abgp.logger.info(`state: ${window.abgp.stateRoot}`);
    self.postMessage({
      type: 'info',
      args: [{stateRoot: window.abgp.stateRoot, lastUpdateTimestamp: window.abgp.lastUpdateTimestamp}]
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
    const packet = new TextDecoder('utf-8').decode(new Uint8Array(e.data.args[0]));
    window.abgp.emitPacket(packet);
  }

  if (e.data.type === 'add_record') {
    return window.abgp.append(...e.data.args);
  }

  if (e.data.type === 'get_records') {
    const records = [...window.abgp.db.values()].map((v)=>({
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
