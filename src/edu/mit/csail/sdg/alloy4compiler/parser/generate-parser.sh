#!/bin/bash

java -jar ../../../../../../../lib/java-cup-11a.jar  \
 -package edu.mit.csail.sdg.alloy4compiler.parser \
 -parser CompParser \
 -progress -time -compact_red \
 -symbols CompSym < Alloy.cup