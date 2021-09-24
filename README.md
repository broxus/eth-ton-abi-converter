## eth-ton-abi-converter

### How to use

1. Install this package:
```bash
npm install --save eth-ton-abi-converter
```

2. Make sure `file-loader` is installed and add the following loader to your `webpack.config.js`:
```js
{
  test: /\.wasm$/,
  type: 'javascript/auto',
  use: [
    {
      loader: 'file-loader',
      options: {
        name: '[name].[hash].[ext]',
        outputPath: 'wasm/',
        esModule: false
      }
    }
  ]
}
```

3. Import and use this package:
```js
import init, { 
    mapTonCellIntoEthBytes, 
    mapEthBytesIntoTonCell 
} from 'eth-ton-abi-converter';

// ...

// NOTE: init must be called only once before the
// first usage of any method from this package
await init();

try {
    // 1. TON -> ETH event data mapping
    const ethBytes = mapTonCellIntoEthBytes(
        '[{"name":"wid","type":"int8"},{"name":"addr","type":"uint256"},{"name":"tokens","type":"uint128"},{"name":"eth_addr","type":"uint160"},{"name":"chainId","type":"uint32"}]',
        'te6ccgEBAQEASwAAkgDgJynpvprQfepGyqb3cIWXUEmxp2eBULCggI5LuGQmvgAAAAAAAAAAAAAAAAAAAEPYQ8xpyP43mAn7dXyTTDEOyJvGPwAAAAM='
    );
    // Will print hex encoded mapped data
    console.log(ethBytes);
    
    // 2. ETH -> TON event data mapping
    const tonCell = mapEthBytesIntoTonCell(
        '{"name":"Deposit","inputs":[{"name":"amount","type":"uint256","indexed":false},{"name":"wid","type":"int128","indexed":false},{"name":"addr","type":"uint256","indexed":false}],"anonymous":false,"type":"event"}',
        '0x00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000a921453472366b7feeec15323a96b5dcf17197c88dc0d4578dfa52900b8a33cb'
    );
    // Will print base64 encoded BOC
    console.log(tonCell);
} catch(e) {
    // All parser errors are thrown as exceptions
    console.error(e);
}
```
