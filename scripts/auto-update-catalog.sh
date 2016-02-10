#! /bin/bash

cd /var/www/html/tde/tde/scripts
./import.py -u
./make-catalog.py
stamp=$(date +"%Y-%m-%d %k:%M")
./commit-and-push-repos.sh "Auto update: $stamp"
