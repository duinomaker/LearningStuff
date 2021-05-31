const ESLintPlugin = require('eslint-webpack-plugin')
const path = require('path')

const mainConfig = {
  target: 'electron-main',
  mode: 'production',
  entry: './src/main.js',
  plugins: [new ESLintPlugin()],
  output: {
    filename: 'main.js',
    path: path.resolve(__dirname, 'public')
  }
}

const preloadConfig = {
  target: 'electron-preload',
  mode: 'production',
  entry: './src/preload.js',
  plugins: [new ESLintPlugin()],
  output: {
    filename: 'preload.js',
    path: path.resolve(__dirname, 'public')
  }
}

const rendererConfig = {
  target: 'electron-renderer',
  mode: 'production',
  entry: './src/renderer.js',
  plugins: [new ESLintPlugin()],
  output: {
    filename: 'renderer.js',
    path: path.resolve(__dirname, 'public')
  }
}

module.exports = [mainConfig, preloadConfig, rendererConfig]
