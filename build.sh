#!/usr/bin/env bash

set -e

# Package name
PKG_NAME="eth_ton_abi_converter"
NPM_PKG_NAME="eth-ton-abi-converter"

# Root dir
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

# Check if jq is installed
if ! [ -x "$(command -v jq)" ]; then
  echo "jq is not installed" >&2
  exit 1
fi

cd "${SCRIPT_DIR}/bindings"

# Clean previous packages
if [ -d "pkg" ]; then
  rm -rf pkg
fi

if [ -d "pkg-node" ]; then
  rm -rf pkg-node
fi

# Build for both targets
wasm-pack build --release -t nodejs -d pkg-node
wasm-pack build --release -t web -d pkg

# Merge nodejs & browser packages
cp "pkg-node/${PKG_NAME}.js" "pkg/${PKG_NAME}_main.js"
cp "pkg-node/${PKG_NAME}.d.ts" "pkg/${PKG_NAME}_main.d.ts"

sed -i "s/__wbindgen_placeholder__/wbg/g" "pkg/${PKG_NAME}_main.js"

jq ".main = \"${PKG_NAME}_main.js\"" pkg/package.json |
  jq ".browser = \"${PKG_NAME}.js\"" |
  jq ".name = \"${NPM_PKG_NAME}\"" >pkg/temp.json
mv pkg/temp.json pkg/package.json

rm -rf pkg-node
