const path = require('path');
const { BundleAnalyzerPlugin } = require('webpack-bundle-analyzer');
const webpack = require('webpack');

const implementations = {
  CryptoPlain: './src/implementation/crypto/plain/index.ts',
  CryptoBNElliptic: './src/implementation/crypto/bnelliptic/index.ts',
  StoragePlain: './src/implementation/storage/PlainStorage.ts'
};

const template = (name, entryPath, outName) => {
  return {
    mode: 'production',
    entry: entryPath,
    module: {
      rules: [
        {
          test: /\.tsx?$/,
          use: 'ts-loader',
          exclude: /node_modules/
        }
      ]
    },
    plugins: [
      new BundleAnalyzerPlugin({
        analyzerMode: 'static',
        reportFilename: path.join(__dirname, `webpack_report_${name.toLowerCase()}.html`)
      }),
      new webpack.ProvidePlugin({
        Buffer: ['buffer', 'Buffer']
      })
    ],
    resolve: {
      extensions: ['.ts', '.js'],
      fallback: {
        crypto: require.resolve('crypto-browserify'),
        stream: require.resolve('stream-browserify'),
        buffer: require.resolve('buffer')
      }
    },
    output: {
      filename: outName,
      path: path.resolve(__dirname, 'dist', 'web'),
      library: name,
      libraryTarget: 'umd'
    }
  };
};

const configs = [
  template('ABGP', './src/consensus/main.ts', 'bundle.js')
];

// eslint-disable-next-line guard-for-in
for (const name in implementations) {
  configs.push(
    template(name, implementations[name], `bundle_${name.toLowerCase()}.js`)
  );
}

module.exports = configs;
