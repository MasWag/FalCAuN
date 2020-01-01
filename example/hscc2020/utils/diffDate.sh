#!/bin/bash -u
#****h* utils/diffDate
# NAME
#  diffDate
# DESCRIPTION
#  take the difference of the given two dates. We assume that the duration is less than 24 hours.
#
# USAGE
#  ./diffDate.sh < <input-file>
#
# EXAMPLE
#  ./diffDate.sh <(echo 04:05:54.631) <(echo 04:08:51.347)
# PORTABILITY
#  We need GNU date. It must be date or gdate.
#******

if date --version 2>&1 | grep GNU >/dev/null; then
    GDATE=date
elif which gdate >/dev/null; then
    GDATE=gdate
else
    echo GNU date is not installed
    exit 1
fi

while read -r line; do
    $GDATE -d "$line" +%s
done | awk 'NR>1{diff = $1-prev;while(diff < 0) {diff += 24 * 60 * 60}; print diff}{prev = $1}'
