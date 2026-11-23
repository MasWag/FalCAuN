#!/bin/sh -u
#****h* utils/check_no_matlab_engine_bundled
# NAME
#  check_no_matlab_engine_bundled
# DESCRIPTION
#  Check that the artifacts of the matlab module do not bundle the MATLAB Engine API for Java (com.mathworks:engine).
#  The Engine API is provided by the user's MATLAB installation and must not be redistributed with FalCAuN.
#  This script fails if
#  - a JAR file in matlab/target contains classes under com/mathworks/,
#  - matlab/target/lib contains a copy of the Engine JAR, or
#  - com.mathworks:engine is not a provided dependency of the matlab module.
#
# USAGE
#  mvn clean --projects matlab && mvn install -DskipTests
#  ./utils/check_no_matlab_engine_bundled.sh
#
#******

cd "$(dirname "$0")/../" || exit 1

target=matlab/target
status=0

fail() {
    echo "NG: $*"
    status=1
}

jars=$(find "$target" -maxdepth 1 -name 'FalCAuN-matlab-*.jar' 2>/dev/null)
if [ -z "$jars" ]; then
    echo "Error: no JAR file of the matlab module in $target. Build it first, e.g., by 'mvn install -DskipTests'"
    exit 1
fi

# The JAR files of the matlab module must not contain classes of MathWorks
for jar in $jars; do
    count=$(unzip -Z1 "$jar" | grep -c '^com/mathworks/')
    if [ "$count" -ne 0 ]; then
        fail "$jar contains $count entries under com/mathworks/"
    else
        echo "OK: $jar contains no entries under com/mathworks/"
    fi
    # Unfold the continuation lines of the manifest
    manifest=$(unzip -p "$jar" META-INF/MANIFEST.MF | tr -d '\r' | awk 'NR > 1 && /^ / {line = line substr($0, 2); next} {if (NR > 1) print line; line = $0} END {print line}')
    echo "    $(echo "$manifest" | grep '^Main-Class:' || echo 'Main-Class: (none)')"
    echo "    Class-Path: $(echo "$manifest" | grep '^Class-Path:' | sed 's/^Class-Path://' | wc -w) entries"
    if echo "$manifest" | grep '^Class-Path:' | grep -q 'engine-[0-9]'; then
        fail "the manifest of $jar refers to the Engine JAR"
    fi
done

# The copied dependencies must not contain the Engine JAR
if [ -d "$target/lib" ]; then
    copied=$(find "$target/lib" -iname '*.jar' | while read -r jar; do
        case "$(basename "$jar")" in
        engine-*.jar) echo "$jar" ;;
        *) unzip -Z1 "$jar" | grep -q '^com/mathworks/' && echo "$jar" ;;
        esac
    done)
    if [ -n "$copied" ]; then
        fail "$target/lib contains the MATLAB Engine API: $copied"
    else
        echo "OK: $target/lib contains no MATLAB Engine API ($(find "$target/lib" -name '*.jar' | wc -l) JAR files)"
    fi
fi

# The Engine API must be a provided dependency
tree=$(mvn -q dependency:tree --projects matlab -Dincludes=com.mathworks -DoutputFile=/dev/stdout 2>&1)
scope=$(echo "$tree" | grep -o 'com\.mathworks:engine:jar:[^:]*:[a-z]*' | awk -F: '{print $5}')
if [ "$scope" = provided ]; then
    echo "OK: com.mathworks:engine is a provided dependency"
else
    fail "com.mathworks:engine is not a provided dependency (scope: '${scope:-not found}')"
    echo "$tree"
fi

exit $status
