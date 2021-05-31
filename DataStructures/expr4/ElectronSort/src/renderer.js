'use strict'

const algorithms = new Map()
algorithms.set('quick', { label: '快速排序', data: [] })
algorithms.set('merge', { label: '归并排序', data: [] })
algorithms.set('heap', { label: '堆排序', data: [] })
algorithms.set('select', { label: '选择排序', data: [] })
algorithms.set('insert', { label: '插入排序', data: [] })
algorithms.set('bubble', { label: '冒泡排序', data: [] })
const lengths = [...Array(100).keys()].map(x => (x + 1) * 100)

function onReceive (result) {
  const data = algorithms.get(result.name).data
  const newPoint = { x: result.length, y: result.duration }
  let i = data.length - 1
  if (i === -1 || data[i].x < result.length) {
    data.push(newPoint)
  } else {
    for (; i !== 0; --i) {
      if (data[i - 1].x < result.length && result.length < data[i].x) {
        break
      }
    }
    data.splice(i, 0, newPoint)
  }
}

const colors = [
  'rgba(255, 99, 132, 1)',
  'rgba(54, 162, 235, 1)',
  'rgba(255, 206, 86, 1)',
  'rgba(75, 192, 192, 1)',
  'rgba(153, 102, 255, 1)',
  'rgba(255, 159, 64, 1)'
]

const ctx = document.getElementById('chart').getContext('2d')
// eslint-disable-next-line no-undef
const lineChart = new Chart(ctx, {
  type: 'line',
  data: {
    datasets: [...algorithms.values()].map((algo, index) => ({
      label: algo.label,
      data: algo.data,
      borderColor: colors[index],
      fill: false,
      parsing: false,
      normalized: true
    }))
  },
  options: {
    scales: {
      xAxes: [{
        type: 'linear'
      }]
    },
    elements: {
      line: {
        tension: 0
      }
    },
    animation: false,
    spanGaps: true
  }
})

window.sorting.evaluate([...algorithms.keys()], lengths, onReceive)
setInterval(() => {
  lineChart.update()
}, 100)
