const path = require('path');
const { BundleAnalyzerPlugin } = require('webpack-bundle-analyzer');

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
      })
    ],
    resolve: {
      extensions: ['.ts', '.js'],
      fallback: {}
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

module.exports = configs;
