#!/bin/bash

if [[ -z "$1" || -z "$2" || -z "$3" || -z "$4" ]];
then
  echo "Need set all parameters: <sec> <cmd> <upper_seed_bound> <query>";
  exit
fi

./runCheck.sh "$1" "$2" "$3" | ./parseAndFindBest.sh "$4"
