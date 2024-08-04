#!/bin/sh

set -e

boogie_file=$1
base=`basename $boogie_file .bpl`
lean_file="$base.lean"
dotnet ../../Source/BoogieDriver/bin/Debug/net8.0/BoogieDriver.dll /printLean:$lean_file $boogie_file
lake env lean $lean_file
