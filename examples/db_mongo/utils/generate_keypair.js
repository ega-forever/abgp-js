const crypto = require('crypto');


const generate = ()=>{
  const node = crypto.createECDH('secp256k1');
  node.generateKeys();

  if (node.getPrivateKey().toString('hex').length !== 64) {
    return generate_keypair();
  }

  console.log({
    privateKey: node.getPrivateKey('hex'),
    publicKey: node.getPublicKey('hex', 'compressed')
  });
}

module.exports = generate();
