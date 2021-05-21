#!/bin/sh

TEMP=/tmp/magic-pager-$RANDOM.txt
tee $TEMP

extract_graph() {
    sed -n "/^digraph G {$/,/^}$/p" $1 | csplit --prefix $1- --suffix-format "%04d.dot" --elide-empty-files - '/^digraph G {$/' '{*}'
    for i in $1-*.dot; do
        dot -Tpng -O $i
    done
}

extract_graph $TEMP
eog $TEMP*.png

rm -f $TEMP*
