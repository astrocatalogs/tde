#!/usr/local/bin/python3.5

import csv
import glob

for file in sorted(glob.glob("../tde-internal/*.dat"), key=lambda s: s.lower()):
    f = open(file,'r')
    tsvin = csv.reader(f, delimiter='\t', skipinitialspace=True)

    for r, row in enumerate(tsvin):
        if row[0] == 'photometry':
