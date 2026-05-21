## QuestPlugin: rewrite `a ? b` → `a`

This plugin rewrites applications of `?` to the first argument.

### Demo

The demo is the test component `example` implemented in `example/Example.hs`:

``` haskell
module Main where

(?) :: a -> b -> a
(?) = undefined

test :: Int
test = 42 ? 41 ? 40

main = putStrLn $ show test
```

By default it builds with the plugin (see the `-fplugin` in `quest-plugin.cabal`) and prints `42`:

``` shellsession
❯ cabal run example
...
42
```

If you turn off the plugin (e.g. comment out the `-fplugin` in the cabal file), it will fail with `undefined`.
