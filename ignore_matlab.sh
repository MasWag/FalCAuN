#!/bin/sh

# remove matlab dependency from pom.xml
TMPFILE=$(mktemp /tmp/pom.xml.XXXXXX) || exit 1
awk '/BEGIN MATLAB/{ignore=1}ignore==0;/END MATLAB/{ignore=0}' pom.xml > $TMPFILE
mv $TMPFILE pom.xml

# remove matlab related files
rm -f ./src/main/java/org/group_mmm/Simulink*
rm -f ./src/main/java/org/group_mmm/*Oracle*

rm -f ./src/test/java/org/group_mmm/Simulink*
rm -f ./src/test/java/org/group_mmm/AutotransExample*
