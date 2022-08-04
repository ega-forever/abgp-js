const path = require('path');
const webpack = require('webpack');

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
      libraryTarget: 'umd',
      libraryExport: 'default'
    }
  };
};

module.exports = template('PlainCrypto', './src/index.ts', 'bundle.js');
