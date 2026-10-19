#!/bin/sh
set -eu

version=2.3
archive=.deps/stdlib-$version.tar.gz
directory=.deps/agda-stdlib-$version
checksum=407286af16f2b5b8aebe577b3610ae9b40ce296ed3c03c66444b5801c2fa3012

if test -f "$directory/standard-library.agda-lib"; then
  exit 0
fi

mkdir -p .deps
curl --fail --location --silent --show-error \
  "https://codeload.github.com/agda/agda-stdlib/tar.gz/refs/tags/v$version" \
  --output "$archive"
echo "$checksum  $archive" | sha256sum --check -
tar -xzf "$archive" -C .deps
rm "$archive"
