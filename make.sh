#!/bin/bash

bash makecoqproject.sh
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile