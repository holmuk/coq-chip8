#!/bin/bash

### This script generates a _CoqProject file

### Variables

DIRS=(lib src)
DIRMAPS=chip8

### Script

COQPROJECT_TMP=_CoqProject.tmp$$

rm -f $COQPROJECT_TMP
touch $COQPROJECT_TMP

for (( i = 0; i < ${#DIRS[@]}; i++)) do
	dir=${DIRS[i]}
	sp=${DIRMAPS}
	echo "-Q $dir $sp" >> $COQPROJECT_TMP
done

for dir in ${DIRS[@]}; do
  echo >> $COQPROJECT_TMP
  find $dir -maxdepth 1 -iname '*.v' -not -name '*\#*' >> $COQPROJECT_TMP
done

### Enlist all *.v files

echo >> $COQPROJECT_TMP
ls | grep "?*.v" >> $COQPROJECT_TMP

mv $COQPROJECT_TMP _CoqProject
