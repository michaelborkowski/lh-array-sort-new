FROM benz0li/ghc-musl:9.10.1

RUN apk upgrade --no-cache \
 && apk add --no-cache \
      z3 git

RUN  mkdir cabal-dir \
  && export CABAL_DIR=/cabal-dir \
  && cabal update \
  && git clone https://github.com/michaelborkowski/lh-array-sort-new.git app \
  && cd app      \
  && cabal configure --constraint="lh-array-sort -liquid-checks +prim-mutable-arrays" --enable-tests \
  && cabal build all \
  && cabal test      \
  && cd ..       \
  && rm -rf /app

CMD ["bash"]
