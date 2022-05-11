const axios = require('axios');


const generate = async () => {
  for (let i = 0; i < 100; i++) {
    const hash = await axios.post('http://localhost:3101/record', {
      key: Math.random().toString(16),
      value: Math.random().toString(16),
      version: 1
    });

    console.log(`[${i}] ${hash.data.hash}`);
  }

}

module.exports = generate();