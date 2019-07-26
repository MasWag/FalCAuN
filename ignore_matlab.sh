#!/bin/sh
#****h* CyVeriA/ignore_matlab
# NAME
#  ignore_matlab
# DESCRIPTION
#  Remove the files that require MATLAB. This script is used for CI.
#
# USAGE
#  ./ignore_matlab.sh
#
#******

# remove matlab dependency from pom.xml
TMPFILE=$(mktemp /tmp/pom.xml.XXXXXX) || exit 1
awk '/BEGIN MATLAB/{ignore=1}ignore==0;/END MATLAB/{ignore=0}' pom.xml > $TMPFILE
mv $TMPFILE pom.xml

# remove matlab related files
rm -f ./src/main/java/org/group_mmm/SimulinkMembershipOracle.java 
rm -f ./src/main/java/org/group_mmm/SimulinkMembershipOracleCost.java 
rm -f ./src/main/java/org/group_mmm/SimulinkSUL.java 
rm -f ./src/main/java/org/group_mmm/SimulinkVerifier.java 
rm -f ./src/main/java/org/group_mmm/Main.java
rm -f ./src/main/java/org/group_mmm/AbstractSelectEQOracle.java
rm -f ./src/main/java/org/group_mmm/GAEQOracle.java
rm -f ./src/main/java/org/group_mmm/HillClimbingEQOracle.java
rm -f ./src/main/java/org/group_mmm/MutateSelectEQOracle.java
rm -f ./src/main/java/org/group_mmm/SAEQOracle.java
rm -f ./src/main/java/org/group_mmm/SimulinkMembershipOracle.java
rm -f ./src/main/java/org/group_mmm/SimulinkMembershipOracleCost.java
rm -f ./src/main/java/org/group_mmm/EQSearchProblem.java
rm -f ./src/main/java/org/group_mmm/SimulinkSteadyStateGeneticAlgorithm.java

rm -f ./src/test/java/org/group_mmm/Simulink*
rm -f ./src/test/java/org/group_mmm/AutotransExample*
rm -f ./src/test/java/org/group_mmm/HillClimbingEQOracleTest.java
