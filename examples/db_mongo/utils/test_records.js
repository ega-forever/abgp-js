const axios = require('axios');
const _ = require('lodash');

const nodes = [
  'http://localhost:3101',
  'http://localhost:3201',
  'http://localhost:3301',
  'http://localhost:3401',
  'http://localhost:3501',
  'http://localhost:3601',
  'http://localhost:3701',
  'http://localhost:3801',
  'http://localhost:3901'
];

const recordsGenerated = 100;

const test = async () => {

  const records = [];

  for (const nodeURI of nodes) {
    const reply = await axios.get(`${nodeURI}/records/range/0/0/${recordsGenerated}`);
    records.push(...reply.data);
  }

  const uniq = _.chain(records)
    .map(r=> r.hash)
    .reduce((res, v)=>{
      res[v] = res[v] ? res[v] + 1 : 1;
      return res;
    }, {})
    .value();

  console.log(uniq);
  console.log(`total keys: ${Object.keys(uniq).length}`);

  const syncedKeysAmount = _.chain(uniq)
    .keys()
    .filter(k=> uniq[k] === nodes.length)
    .size()
    .value();

  console.log(`synced ${syncedKeysAmount} of ${Object.keys(uniq).length}`);

}

module.exports = test();