const path = require('path');
const { BundleAnalyzerPlugin } = require('webpack-bundle-analyzer');
const webpack = require('webpack');

module.exports = {
  mode: 'production',
  entry: './src/consensus/main.ts',
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
      reportFilename: path.join(__dirname, 'webpack_report.html')
    }),
    new webpack.ProvidePlugin({
      Buffer: ['buffer', 'Buffer']
    })
  ],
  resolve: {
    extensions: ['.ts', '.js'],
    fallback: {
      fs: false,
      tls: false,
      net: false,
      path: false,
      zlib: false,
      http: false,
      https: false,
      stream: false,
      buffer: require.resolve('buffer'),
      crypto: require.resolve('crypto-browserify') // if you want to use this module also don't forget npm i crypto-browserify
    }
  },
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'dist', 'web'),
    library: 'ABGP',
    libraryTarget: 'umd'
  }
};
