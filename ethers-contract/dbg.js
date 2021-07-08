const ethers = require("ethers")
const bigint = ethers.BigNumber
console.log(bigint)
const abi = require("./abi.json")

const iface = new ethers.utils.Interface(abi)

// g2
b = [
  [
    "1",
    "2",

  ],
  [
    "3",
    "4",
  ]
]

// F
inputs = [
  "5",
]

const args = [
  b,
  inputs
]

const data = iface.encodeFunctionData(
  "myVerify",
  args,
)
console.log(data)
