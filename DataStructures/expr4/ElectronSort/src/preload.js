'use strict'

const { contextBridge } = require('electron')
const { spawn } = require('child_process')
const path = require('path')

function getProgram () {
  function fixPathForAsarUnpack (path) {
    return path.replace('app.asar', 'app.asar.unpacked')
  }
  if (process.platform === 'darwin') {
    console.log('the platform is macOS')
    return fixPathForAsarUnpack(path.join(__dirname, 'static/cpp_sort-mac'))
  }
  if (process.platform === 'linux') {
    console.log('the platform is Linux')
    return fixPathForAsarUnpack(path.join(__dirname, 'static/cpp_sort-linux'))
  }
  if (process.platform === 'win32') {
    console.log('the platform is Windows')
    return fixPathForAsarUnpack(path.join(__dirname, 'static/cpp_sort.exe'))
  }
}

contextBridge.exposeInMainWorld('sorting', {
  evaluate: (names, lengths, send) => {
    function hexToFloat64 (hex) {
      const buffer = new ArrayBuffer(8)
      const dataView = new DataView(buffer)
      dataView.setBigUint64(0, hex)
      return dataView.getFloat64()
    }
    const proc = spawn(getProgram())
    const decoder = new TextDecoder('utf-8')
    proc.stdout.on('data', (data) => {
      const text = decoder.decode(data)
      text.split('\n').forEach((line) => {
        if (line.length) {
          const parts = line.split(',')
          send({
            name: parts[0],
            length: parseInt(parts[1]),
            duration: hexToFloat64(parts[2])
          })
        }
      })
    })
    proc.once('close', (code) => {
      console.log(`child process exited with code ${code}`)
    })
    proc.stdin.cork()
    proc.stdin.write(names.join(' ') + ' ' + lengths.join(' '))
    proc.stdin.uncork()
    proc.stdin.end()
  }
})
