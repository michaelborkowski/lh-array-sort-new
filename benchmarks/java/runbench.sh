#!/usr/bin/env sh

mvn compile exec:java "-Dexec.args=$1 $2" -Dexec.mainClass=array.bench.Main
