#!/bin/sh
exec java -Xmx8g -jar "${FLIX_JAR:-/home/user/tools/flix/flix.jar}" "$(dirname "$0")/mcfa.flix" -- "$@"
