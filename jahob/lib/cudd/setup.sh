#! /bin/sh
CREATE="ln -s"
if test -d lib 
  then 
    : 
  else 
    mkdir lib 
fi
if test -d include
  then
    :
  else
    mkdir include
    cd include
    $CREATE ../cudd/cudd.h .
    $CREATE ../cudd/cuddInt.h .
    $CREATE ../dddmp/dddmp.h .
    $CREATE ../mtr/mtr.h .
    $CREATE ../st/st.h .
    $CREATE ../util/util.h .
    $CREATE ../obj/cuddObj.hh .
    $CREATE ../mnemosyne/mnemosyne.h .
fi
