#!/bin/bash

java -jar ../../../../../../../lib/jflex-1.6.0.jar --nobak -d . Alloy.lex

sed -i 's/public java_cup.runtime.Symbol next_token() throws java.io.IOException/public java_cup.runtime.Symbol next_token() throws java.io.IOException, Err/' CompLexer.java

