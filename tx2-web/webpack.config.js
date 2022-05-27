const HtmlWebpackPlugin = require('html-webpack-plugin');
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const path = require("path");

module.exports = {
  entry: "./src/index.tsx",
  output: {
    path: path.resolve(__dirname, "dist"),
    filename: "bundle.[hash].js"
  },
  devServer: {
    compress: true,
      port: 8081,
    hot: true,
    static: './dist',
    historyApiFallback: true,
    open: true
  },
  resolve: {
    extensions: ['.tsx', '.ts', '.js', '.json', '.wasm'],
  },
  module: {
    rules: [
	{
            test: /.(t|j)(s|sx)$/,
            exclude: /node_modules/,
            use: {
		loader: "ts-loader"
            }
	},
	{
	    enforce: 'pre',
	    test: /\.js$/,
	    loader: 'source-map-loader'
	}
    ]
  },
  plugins: [
    new HtmlWebpackPlugin({
      template: __dirname + "/public/index.html",
      filename: "index.html"
    }),
    new WasmPackPlugin({
      crateDirectory: path.resolve(__dirname, ".")
    }),
  ],
  mode: "development",
  devtool: 'inline-source-map',
  experiments: {
    asyncWebAssembly: true,
  },
};
