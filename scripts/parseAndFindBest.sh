#!/bin/bash

#
# Handles the output of ./runCheck.sh _ "stack exec -- ukt" _
#
# Format of the output
# Original -> Depth: _ Leafs: _ Nodes: _
# Marked   -> Depth: _ Leafs: _ Fail: _ Success _ Nodes _ FunCallNodes: _
# Cut      -> Depth: _ Leafs: _ Fail: _ Success _ Nodes _ FunCallNodes: _
# ^ seed: _
#
# More general:
#
# (<name of the line> -> (<name of the field>: <number>)+\n)+
# ^ seed: <number>
#
#
# Optimization request: <name of the line>:<name of the field>
# Example: Cut:Depth
#          Cut:Success
#
#

# $1 -- query

query="$1"

# Seems to be the most stupid way to do it.
IFS=':'
read -ra arr <<< "$query"
line=${arr[0]}
field=${arr[1]}
IFS=''

[[ -z "$line" || -z "$field" ]] && echo "Unable to address an optimization value" && exit

function parse_seed {
  sed -re 's/\^ *seed: *//;' <<< "$1"
}

function find_field {
  regex="s/^.*"$field": *([0-9]+).*/\1/"
  sed -re "$regex"
}

declare -a field_and_seed
field_and_seed=()

function handle {
  while read lineWithOriginal
  do 
    read lineWithMarked
    read lineWithCut
    read lineWithSeed
    read newLine
 
    #echo "Original: " $lineWithOriginal
    #echo "Marked: " $lineWithMarked
    #echo "Cut: " $lineWithCut
  
    seed=$(parse_seed "$lineWithSeed")
    #echo "Seed:" $seed  
    local value=0
    case "$line" in
       "Original") value=$(find_field <<< "$lineWithOriginal");;
       "Marked")   value=$(find_field <<< "$lineWithMarked");;
       "Cut"*)     value=$(find_field <<< "$lineWithCut");;
       *) echo ":c";;
    esac
   #echo "Value:" $value
   field_and_seed+=("$value $seed")
  done

  #for l in ${field_and_seed[*]}; do echo $l; done | sort -n | head -n 1
  for l in ${field_and_seed[*]}; do echo $l; done | sort -n | head -n 1 | xargs echo "Best value for a field <$field> and its seed:";
  #echo "Best value with seed:" "$res"

}

tail -n +4 | handle
