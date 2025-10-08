#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

if command -v gtar >/dev/null ; then
  # On MacOS, run "sudo brew install gnu-tar" to obtain gtar.
  TAR=gtar
else
  TAR=tar
fi

ARCHIVE=blaze

rm -rf $ARCHIVE $ARCHIVE.tar.gz

mkdir $ARCHIVE

cp -r \
  README.md \
  LICENSE \
  src \
  theories \
  opam \
  setup.sh \
  Makefile \
  _CoqProject \
  $ARCHIVE

$TAR cvfz $ARCHIVE.tar.gz \
  --exclude-ignore-recursive=.gitignore \
  --owner=0 --group=0 \
  $ARCHIVE

rm -rf $ARCHIVE
