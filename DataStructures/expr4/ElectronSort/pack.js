'use strict'

const webpack = require('webpack')
const config = require('./webpack.config')
const fse = require('fs-extra')
const path = require('path')

fse.emptyDirSync('public')

const assets = [
  'static',
  'src/index.html',
  'src/style.css',
  'node_modules/chart.js/dist/Chart.min.js'
]

assets.forEach(asset => {
  const dest = 'public/' + path.basename(asset)
  fse.copySync(asset, dest, { overwrite: true }, err => {
    console.error(err)
  })
})

webpack(config, (err, stats) => {
  if (err || stats.hasErrors()) {
    console.error(err)
  }

  console.log(stats.toString({
    colors: true
  }))

  process.exit()
})
