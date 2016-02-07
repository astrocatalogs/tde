#!/usr/local/bin/python3.5

import csv
import glob
import os
import re
import urllib.request
import calendar
import sys
import json
import codecs
import resource
import argparse
from cdecimal import Decimal
from astroquery.vizier import Vizier

from astropy.time import Time as astrotime
from astropy.cosmology import Planck15 as cosmo
from collections import OrderedDict
from math import log10, floor, sqrt, isnan
from bs4 import BeautifulSoup, Tag, NavigableString
from string import ascii_letters

parser = argparse.ArgumentParser(description='Generate a catalog JSON file and plot HTML files from TDE data.')
parser.add_argument('--update', '-u', dest='update', help='Only update catalog using live sources.',    default=False, action='store_true')
args = parser.parse_args()

clight = 29979245800.

eventnames = []

tasks = {
    "internal":       {"update": False},
    "old-tdefit":     {"update": False},
    "vizier":         {"update": False},
    "ogle":           {"update": True },
    "writeevents":    {"update": True }
}

events = OrderedDict()

with open('rep-folders.txt', 'r') as f:
    repfolders = f.read().splitlines()

repyears = [int(repfolders[x][-4:]) for x in range(len(repfolders))]
repyears[0] -= 1

typereps = {
    'I P':    ['I pec', 'I-pec', 'I Pec', 'I-Pec'],
    'Ia P':   ['Ia pec', 'Ia-pec', 'Iapec'],
    'Ib P':   ['Ib pec', 'Ib-pec'],
    'Ic P':   ['Ic pec', 'Ic-pec'],
    'Ib/c':   ['Ibc'],
    'Ib/c P': ['Ib/c-pec'],
    'II P':   ['II pec', 'IIpec', 'II Pec', 'IIPec', 'IIP', 'IIp', 'II p', 'II-pec', 'II P pec', 'II-P'],
    'II L':   ['IIL'],
    'IIn P':  ['IIn pec', 'IIn-pec'],
    'IIb P':  ['IIb-pec', 'IIb: pec']
}

repbetterquanta = {
    'redshift',
    'ebv',
    'hvel',
    'lumdist'
}

def event_attr_priority(attr):
    if attr == 'photometry' or attr == 'spectra':
        return 'zzzzzzzz'
    if attr == 'name':
        return 'aaaaaaaa'
    if attr == 'aliases':
        return 'aaaaaaab'
    if attr == 'sources':
        return 'aaaaaaac'
    return attr

def add_event(name, load = True, delete = True):
    if name not in events or 'stub' in events[name]:
        if load:
            newname = load_event_from_file(name = name, delete = delete)
            if newname:
                if 'stub' in events[newname]:
                    raise(ValueError('Failed to find event file for stubbed event'))
                print('Loaded event ' + newname)
                return newname

        matches = []
        for event in events:
            if len(events[event]['aliases']) > 1 and name in events[event]['aliases']:
                matches.append(event)
        if len(matches) == 1:
            return matches[0]
        elif len(matches) > 1:
            raise(ValueError('Error, multiple matches to event, need event merging'))
        events[name] = OrderedDict()
        events[name]['name'] = name
        add_alias(name, name)
        print('Added new event ' + name)
        return name
    else:
        return name

def event_filename(name):
    return(name.replace('/', '_'))

def add_alias(name, alias):
    if 'aliases' in events[name]:
        if alias not in events[name]['aliases']:
            events[name].setdefault('aliases',[]).append(alias)
    else:
        events[name]['aliases'] = [alias]

def snname(string):
    newstring = string.replace(' ', '').upper()
    if (newstring[:2] == "SN"):
        head = newstring[:6]
        tail = newstring[6:]
        if len(tail) >= 2 and tail[1] != '?':
            tail = tail.lower()
        newstring = head + tail

    return newstring

def get_sig_digits(x):
    return len((''.join(x.split('.'))).strip('0'))

def round_sig(x, sig=4):
    if x == 0.0:
        return 0.0
    return round(x, sig-int(floor(log10(abs(x))))-1)

def pretty_num(x, sig=4):
    return str('%g'%(round_sig(x, sig)))

def get_source(name, reference = '', url = '', bibcode = '', secondary = ''):
    nsources = len(events[name]['sources']) if 'sources' in events[name] else 0
    if not reference:
        if not bibcode:
            raise(ValueError('Bibcode must be specified if name is not.'))
        else:
            if url:
                print('Warning: Reference URL ignored if bibcode specified')
        reference = bibcode
        url = "http://adsabs.harvard.edu/abs/" + bibcode
    if 'sources' not in events[name] or reference not in [events[name]['sources'][x]['name'] for x in range(nsources)]:
        source = str(nsources + 1)
        newsource = OrderedDict()
        newsource['name'] = reference
        if url:
            newsource['url'] = url
        if bibcode:
            newsource['bibcode'] = bibcode
        newsource['alias'] =  source
        if secondary:
            newsource['secondary'] = True
        events[name].setdefault('sources',[]).append(newsource)
    else:
        sourcexs = range(nsources)
        source = [events[name]['sources'][x]['alias'] for x in sourcexs][
            [events[name]['sources'][x]['name'] for x in sourcexs].index(reference)]
    return source

def add_photometry(name, timeunit = "MJD", time = "", instrument = "", band = "", magnitude = "", e_magnitude = "", source = "",
        counts = "", e_counts = "", upperlimit = False, system = "", restframe = False, hostnhcorr = False):
    if not time or (not magnitude and not counts):
        print('Warning: Time or AB mag/counts not specified when adding photometry.\n')
        print('Name : "' + name + '", Time: "' + time + '", Band: "' + band + '", AB mag: "' + magnitude + '"')
        return

    if not is_number(time) or (not is_number(magnitude) and not is_number(counts)):
        print('Warning: Time or AB mag not numerical.\n')
        print('Name : "' + name + '", Time: "' + time + '", Band: "' + band + '", AB mag: "' + magnitude + '"')
        return

    if e_magnitude and not is_number(e_magnitude):
        print('Warning: AB error not numerical.\n')
        print('Name : "' + name + '", Time: "' + time + '", Band: "' + band + '", AB err: "' + e_magnitude + '"')
        return

    if e_counts and not is_number(e_counts):
        print('Warning: AB error not numerical.\n')
        print('Name : "' + name + '", Time: "' + time + '", Band: "' + band + '", Count err: "' + e_counts + '"')
        return

    # Look for duplicate data and don't add if duplicate
    if 'photometry' in events[name]:
        for photo in events[name]['photometry']:
            if 'magnitude' in photo and magnitude:
                if (photo['timeunit'] == timeunit and
                    Decimal(photo['time']) == Decimal(time) and
                    Decimal(photo['magnitude']) == Decimal(magnitude) and
                    (('band' not in photo and not band) or
                     ('band' in photo and photo['band'] == band) or
                     ('band' in photo and not band)) and
                    (('e_magnitude' not in photo and not e_magnitude) or
                     ('e_magnitude' in photo and e_magnitude and Decimal(photo['e_magnitude']) == Decimal(e_magnitude)) or
                     ('e_magnitude' in photo and not e_magnitude)) and
                    (('system' not in photo and not system) or
                     ('system' in photo and photo['system'] == system) or
                     ('system' in photo and not system))):
                    return
            elif 'counts' in photo and counts:
                if (photo['timeunit'] == timeunit and
                    Decimal(photo['time']) == Decimal(time) and
                    Decimal(photo['counts']) == Decimal(counts) and
                    (('band' not in photo and not band) or
                     ('band' in photo and photo['band'] == band) or
                     ('band' in photo and not band)) and
                    (('e_counts' not in photo and not e_counts) or
                     ('e_counts' in photo and e_counts and Decimal(photo['e_counts']) == Decimal(e_counts)) or
                     ('e_counts' in photo and not e_counts)) and
                    (('system' not in photo and not system) or
                     ('system' in photo and photo['system'] == system) or
                     ('system' in photo and not system))):
                    return

    photoentry = OrderedDict()
    photoentry['timeunit'] = timeunit
    photoentry['time'] = str(time)
    if band:
        photoentry['band'] = band
    if system:
        photoentry['system'] = system
    if magnitude:
        photoentry['magnitude'] = str(magnitude)
    if e_magnitude:
        photoentry['e_magnitude'] = str(e_magnitude)
    if counts:
        photoentry['counts'] = str(counts)
    if e_counts:
        photoentry['e_counts'] = str(e_counts)
    if instrument:
        photoentry['instrument'] = instrument
    if source:
        photoentry['source'] = source
    if upperlimit:
        photoentry['upperlimit'] = upperlimit
    if restframe:
        photoentry['restframe'] = restframe
    if hostnhcorr:
        photoentry['hostnhcorr'] = hostnhcorr
    events[name].setdefault('photometry',[]).append(photoentry)

def add_spectrum(name, waveunit, fluxunit, wavelengths, fluxes, timeunit = "", time = "", instrument = "",
    deredshifted = "", dereddened = "", errorunit = "", errors = "", source = "", snr = "",
    observer = "", reducer = ""):
    if not waveunit:
        'Warning: No error unit specified, not adding spectrum.'
        return
    if not fluxunit:
        'Warning: No flux unit specified, not adding spectrum.'
        return
    spectrumentry = OrderedDict()
    if deredshifted != '':
        spectrumentry['deredshifted'] = deredshifted
    if dereddened != '':
        spectrumentry['dereddened'] = dereddened
    if instrument:
        spectrumentry['instrument'] = instrument
    if timeunit:
        spectrumentry['timeunit'] = timeunit
    if time:
        spectrumentry['time'] = time
    if snr:
        spectrumentry['snr'] = snr
    if observer:
        spectrumentry['observer'] = observer
    if reducer:
        spectrumentry['reducer'] = reducer

    spectrumentry['waveunit'] = waveunit
    spectrumentry['fluxunit'] = fluxunit
    if errors and max([float(x) for x in errors]) > 0.:
        if not errorunit:
            'Warning: No error unit specified, not adding spectrum.'
            return
        spectrumentry['errorunit'] = errorunit
        data = [wavelengths, fluxes, errors]
    else:
        data = [wavelengths, fluxes]
    spectrumentry['data'] = [list(i) for i in zip(*data)]
    if source:
        spectrumentry['source'] = source
    events[name].setdefault('spectra',[]).append(spectrumentry)

def add_quanta(name, quanta, value, sources, forcereplacebetter = False, error = '', unit = '', kind = ''):
    if not quanta:
        raise(ValueError('Quanta must be specified for add_quanta.'))
    svalue = value.strip()
    serror = error.strip()
    if not svalue or svalue == '--' or svalue == '-':
        return
    if serror and (not is_number(serror) or float(serror) < 0.):
        raise(ValueError('Quanta error value must be a number and positive.'))

    #Handle certain quanta
    if quanta == 'hvel' or quanta == 'redshift':
        if not is_number(value):
            return
    if quanta == 'host':
        svalue = svalue.strip("()")
        svalue = svalue.replace("NGC", "NGC ")
        svalue = svalue.replace("UGC", "UGC ")
        svalue = svalue.replace("IC", "IC ")
        svalue = svalue.replace("Mrk", "MRK")
        svalue = svalue.replace("MRK", "MRK ")
        svalue = svalue.replace("PGC", "PGC ")
        svalue = ' '.join(svalue.split())
    elif quanta == 'claimedtype':
        for rep in typereps:
            if svalue in typereps[rep]:
                svalue = rep
                break
    elif quanta == 'snra' or quanta == 'sndec' or quanta == 'galra' or quanta == 'galdec':
        if unit == 'decdeg' or unit == 'radeg':
            deg = float('%g' % Decimal(svalue))
            sig = get_sig_digits(svalue)
            if unit == 'radeg':
                flhours = deg / 360.0 * 24.0
                hours = floor(flhours)
                minutes = floor((flhours - hours) * 60.0)
                seconds = (flhours * 60.0 - (hours * 60.0 + minutes)) * 60.0
                svalue = str(hours).zfill(2) + ':' + str(minutes).zfill(2) + ':' + pretty_num(seconds, sig = sig - 3).zfill(2)
            if unit == 'decdeg':
                fldeg = abs(deg)
                degree = floor(fldeg)
                minutes = floor((fldeg - degree) * 60.0)
                seconds = (fldeg * 60.0 - (degree * 60.0 + minutes)) * 60.0
                svalue = ('+' if deg >= 0.0 else '-') + str(degree).strip('+-').zfill(2) + ':' + str(minutes).zfill(2) + ':' + pretty_num(seconds, sig = sig - 3).zfill(2)
        elif unit == 'decdms':
            svalue = svalue.replace(' ', ':')
            valuesplit = svalue.split(':')
            svalue = ('+' if float(valuesplit[0]) > 0.0 else '-') + valuesplit[0].strip('+-').zfill(2) + ':' + ':'.join(valuesplit[1:]) if len(valuesplit) > 1 else ''
        elif unit == 'ranospace':
            svalue = svalue[:2] + ':' + svalue[2:4] + ((':' + svalue[4:]) if len(svalue) > 4 else '')
        elif unit == 'decnospace':
            svalue = svalue[:3] + ':' + svalue[3:5] + ((':' + svalue[5:]) if len(svalue) > 5 else '')
        else:
            svalue = svalue.replace(' ', ':')

    if is_number(svalue):
        svalue = '%g' % Decimal(svalue)
    if serror:
        serror = '%g' % Decimal(serror)

    if quanta in events[name]:
        for i, ct in enumerate(events[name][quanta]):
            if ct['value'] == svalue and sources:
                for source in sources.split(','):
                    if source not in events[name][quanta][i]['source'].split(','):
                        events[name][quanta][i]['source'] += ',' + source
                        if serror and 'error' not in events[name][quanta][i]:
                            events[name][quanta][i]['error'] = serror
                return

    quantaentry = OrderedDict()
    quantaentry['value'] = svalue
    if serror:
        quantaentry['error'] = serror
    if sources:
        quantaentry['source'] = sources
    if kind:
        quantaentry['kind'] = kind
    if (forcereplacebetter or quanta in repbetterquanta) and quanta in events[name]:
        newquantas = []
        isworse = True
        newsig = get_sig_digits(svalue)
        for ct in events[name][quanta]:
            if 'error' in ct:
                if serror:
                    if float(serror) < float(ct['error']):
                        isworse = False
                        continue
                newquantas.append(ct)
            else:
                if serror:
                    isworse = False
                    continue
                oldsig = get_sig_digits(ct['value'])
                if oldsig >= newsig:
                    newquantas.append(ct)
                if newsig >= oldsig:
                    isworse = False
        if not isworse:
            newquantas.append(quantaentry)
        events[name][quanta] = newquantas
    else:
        events[name].setdefault(quanta,[]).append(quantaentry)

def get_max_light(name):
    if 'photometry' not in events[name]:
        return (None, None)

    eventphoto = [(x['timeunit'], x['time'], Decimal(x['magnitude'])) for x in events[name]['photometry'] if 'magnitude' in x]
    if not eventphoto:
        return (None, None)
    mlmag = min([x[2] for x in eventphoto])

    mlindex = [x[2] for x in eventphoto].index(mlmag)
    if eventphoto[mlindex][0] == 'MJD':
        mlmjd = float(eventphoto[mlindex][1])
        return (astrotime(mlmjd, format='mjd').datetime, mlmag)
    else:
        return (None, mlmag)

def get_first_light(name):
    if 'photometry' not in events[name]:
        return None

    eventtime = [Decimal(x['time']) for x in events[name]['photometry'] if 'upperlimit' not in x and 'timeunit' in x and x['timeunit'] == 'MJD']
    if not eventtime:
        return None
    flindex = eventtime.index(min(eventtime))
    flmjd = float(eventtime[flindex])
    return astrotime(flmjd, format='mjd').datetime

def set_first_max_light(name):
    if 'maxappmag' not in events[name]:
        (mldt, mlmag) = get_max_light(name)
        if mldt:
            add_quanta(name, 'maxyear', pretty_num(mldt.year), 'D')
            add_quanta(name, 'maxmonth', pretty_num(mldt.month), 'D')
            add_quanta(name, 'maxday', pretty_num(mldt.day), 'D')
            add_quanta(name, 'maxdate', str(mldt.year) + '/' + str(mldt.month).zfill(2) + '/' + str(mldt.day).zfill(2), 'D')
        if mlmag:
            add_quanta(name, 'maxappmag', pretty_num(mlmag), 'D')
    elif 'maxyear' in events[name] and 'maxmonth' in events[name] and 'maxday' in events[name]:
        if (events[name]['maxyear'][0]['source'] == events[name]['maxmonth'][0]['source'] and
            events[name]['maxyear'][0]['source'] == events[name]['maxday'][0]['source']):
            source = events[name]['maxyear'][0]['source']
        else:
            source = 'D'
        add_quanta(name, 'maxdate', events[name]['maxyear'][0]['value'] + '/' + events[name]['maxmonth'][0]['value'].zfill(2) +
            '/' + events[name]['maxday'][0]['value'].zfill(2), source)

    if 'discovermonth' not in events[name] or 'discoverday' not in events[name]:
        fldt = get_first_light(name)
        if fldt:
            add_quanta(name, 'discoveryear', pretty_num(fldt.year), 'D')
            add_quanta(name, 'discovermonth', pretty_num(fldt.month), 'D')
            add_quanta(name, 'discoverday', pretty_num(fldt.day), 'D')
            add_quanta(name, 'discoverdate', str(fldt.year) + '/' + str(fldt.month).zfill(2) + '/' + str(fldt.day).zfill(2), 'D')
    elif 'discoveryear' in events[name] and 'discovermonth' in events[name] and 'discoverday' in events[name]:
        if (events[name]['discoveryear'][0]['source'] == events[name]['discovermonth'][0]['source'] and
            events[name]['discoveryear'][0]['source'] == events[name]['discoverday'][0]['source']):
            source = events[name]['discoveryear'][0]['source']
        else:
            source = 'D'
        add_quanta(name, 'discoverdate', events[name]['discoveryear'][0]['value'] + '/' + events[name]['discovermonth'][0]['value'].zfill(2) +
            '/' + events[name]['discoverday'][0]['value'].zfill(2), source)

def jd_to_mjd(jd):
    return jd - Decimal(2400000.5)

def utf8(x):
    return str(x, 'utf-8')

def is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def convert_aq_output(row):
    return OrderedDict([(x, str(row[x]) if is_number(row[x]) else row[x]) for x in row.colnames])

def derive_and_sanitize():
    # Calculate some columns based on imported data, sanitize some fields
    for name in events:
        set_first_max_light(name)
        if 'claimedtype' in events[name]:
            events[name]['claimedtype'][:] = [ct for ct in events[name]['claimedtype'] if (ct['value'] != '?' and ct['value'] != '-')]
        if 'redshift' in events[name] and 'hvel' not in events[name]:
            # Find the "best" redshift to use for this
            bestsig = 0
            for z in events[name]['redshift']:
                sig = get_sig_digits(z['value'])
                if sig > bestsig:
                    bestz = z['value']
                    bestsig = sig
            if bestsig > 0:
                bestz = float(bestz)
                add_quanta(name, 'hvel', pretty_num(clight/1.e5*((bestz + 1.)**2. - 1.)/
                    ((bestz + 1.)**2. + 1.), sig = bestsig), 'D')
        elif 'hvel' in events[name] and 'redshift' not in events[name]:
            # Find the "best" hvel to use for this
            bestsig = 0
            for hv in events[name]['hvel']:
                sig = get_sig_digits(hv['value'])
                if sig > bestsig:
                    besthv = hv['value']
                    bestsig = sig
            if bestsig > 0 and is_number(besthv):
                voc = float(besthv)*1.e5/clight
                add_quanta(name, 'redshift', pretty_num(sqrt((1. + voc)/(1. - voc)) - 1., sig = bestsig), 'D')
        if 'maxabsmag' not in events[name] and 'maxappmag' in events[name] and 'lumdist' in events[name]:
            # Find the "best" distance to use for this
            bestsig = 0
            for ld in events[name]['lumdist']:
                sig = get_sig_digits(ld['value'])
                if sig > bestsig:
                    bestld = ld['value']
                    bestsig = sig
            if bestsig > 0 and is_number(bestld) and float(bestld) > 0.:
                add_quanta(name, 'maxabsmag', pretty_num(float(events[name]['maxappmag'][0]['value']) -
                    5.0*(log10(float(bestld)*1.0e6) - 1.0), sig = bestsig), 'D')
        if 'redshift' in events[name]:
            # Find the "best" redshift to use for this
            bestsig = 0
            for z in events[name]['redshift']:
                sig = get_sig_digits(z['value'])
                if sig > bestsig:
                    bestz = z['value']
                    bestsig = sig
            if bestsig > 0 and float(bestz) > 0.:
                if 'lumdist' not in events[name]:
                    dl = cosmo.luminosity_distance(float(bestz))
                    add_quanta(name, 'lumdist', pretty_num(dl.value, sig = bestsig), 'D')
                    if 'maxabsmag' not in events[name] and 'maxappmag' in events[name]:
                        add_quanta(name, 'maxabsmag', pretty_num(float(events[name]['maxappmag'][0]['value']) -
                            5.0*(log10(dl.to('pc').value) - 1.0), sig = bestsig), 'D')
        if 'photometry' in events[name]:
            events[name]['photometry'].sort(key=lambda x: (float(x['time']),
                x['band'] if 'band' in x else '', float(x['magnitude'] if 'magnitude' in x else x['counts'])))
        if 'spectra' in events[name] and list(filter(None, ['time' in x for x in events[name]['spectra']])):
            events[name]['spectra'].sort(key=lambda x: float(x['time']))
        events[name] = OrderedDict(sorted(events[name].items(), key=lambda key: event_attr_priority(key[0])))

def delete_old_event_files():
    # Delete all old event JSON files
    for folder in repfolders:
        filelist = glob.glob("../" + folder + "/*.json") + glob.glob("../" + folder + "/*.json.gz")
        for f in filelist:
            os.remove(f)

def write_all_events(empty = False):
    # Write it all out!
    for name in events:
        if 'stub' in events[name]:
            if not empty:
                continue
            else:
                del(events[name]['stub'])
        print('Writing ' + name)
        filename = event_filename(name)

        jsonstring = json.dumps({name:events[name]}, indent='\t', separators=(',', ':'), ensure_ascii=False)

        outdir = '../'
        if 'discoveryear' in events[name]:
            for r, year in enumerate(repyears):
                if int(events[name]['discoveryear'][0]['value']) <= year:
                    outdir += repfolders[r]
                    break
        else:
            outdir += str(repfolders[0])

        f = codecs.open(outdir + '/' + filename + '.json', 'w', encoding='utf8')
        f.write(jsonstring)
        f.close()

def load_event_from_file(name = '', location = '', clean = False, delete = True):
    if not name and not location:
        raise ValueError('Either event name or location must be specified to load event')

    if location:
        path = location
    else:
        indir = '../'
        path = ''
        for rep in repfolders:
            newpath = indir + rep + '/' + name + '.json'
            if os.path.isfile(newpath):
                path = newpath

    if not path:
        return False
    else:
        with open(path, 'r') as f:
            if name in events:
                del events[name]
            events.update(json.loads(f.read(), object_pairs_hook=OrderedDict))
            name = next(reversed(events))
            if clean:
                clean_event(name)
        if 'writeevents' in tasks and delete:
            os.remove(path)
        return name

def clean_event(name):
    bibcodes = []
    if 'name' not in events[name]:
        events[name]['name'] = name
    if 'aliases' not in events[name]:
        add_alias(name, name)
    if 'sources' in events[name]:
        for s, source in enumerate(events[name]['sources']):
            if 'bibcode' in source and 'name' not in source:
                bibcodes.append(source['bibcode'])
        if bibcodes:
            del events[name]['sources']
            for bibcode in bibcodes:
                get_source(name, bibcode = bibcode)
    if 'photometry' in events[name]:
        for p, photo in enumerate(events[name]['photometry']):
            if photo['timeunit'] == 'JD':
                events[name]['photometry'][p]['timeunit'] = 'MJD'
                events[name]['photometry'][p]['time'] = str(jd_to_mjd(Decimal(photo['time'])))
            if bibcodes and 'source' not in photo:
                alias = get_source(name, bibcode = bibcodes[0])
                events[name]['photometry'][p]['source'] = alias

def do_task(task):
    return task in tasks and (not args.update or tasks[task]['update'])

def journal_events(clear = True):
    if 'writeevents' in tasks:
        write_all_events()
    if clear:
        clear_events()

def clear_events():
    global events
    events = OrderedDict((k, OrderedDict((('name', events[k]['name']), ('aliases', events[k]['aliases']), ('stub', True)))) for k in events)

# Either load stubs of each event (if updating) or delete all event files (if starting fresh)
if 'writeevents' in tasks:
    if args.update:
        files = []
        for rep in repfolders:
            files += glob.glob('../' + rep + "/*.json")

        for fi in files:
            name = os.path.basename(os.path.splitext(fi)[0])
            name = add_event(name, delete = False)
            events[name] = OrderedDict((('name', events[name]['name']), ('aliases', events[name]['aliases']), ('stub', True)))
    else:
        delete_old_event_files()

# Import data provided directly to OSC
if do_task('internal'):
    for datafile in sorted(glob.glob("../tde-internal/*.json"), key=lambda s: s.lower()):
        if not load_event_from_file(location = datafile, clean = True, delete = False):
            raise IOError('Failed to find specified file.')
    journal_events()

if do_task('old-tdefit'):
    oldbanddict = {
        "Pg": {"instrument":"Pan-STARRS1", "band":"g"},
        "Pr": {"instrument":"Pan-STARRS1", "band":"r"},
        "Pi": {"instrument":"Pan-STARRS1", "band":"i"},
        "Pz": {"instrument":"Pan-STARRS1", "band":"z"},
        "Mu": {"instrument":"MegaCam",     "band":"u"},
        "Mg": {"instrument":"MegaCam",     "band":"g"},
        "Mr": {"instrument":"MegaCam",     "band":"r"},
        "Mi": {"instrument":"MegaCam",     "band":"i"},
        "Mz": {"instrument":"MegaCam",     "band":"z"},
        "Su": {"instrument":"SDSS",        "band":"u"},
        "Sg": {"instrument":"SDSS",        "band":"g"},
        "Sr": {"instrument":"SDSS",        "band":"r"},
        "Si": {"instrument":"SDSS",        "band":"i"},
        "Sz": {"instrument":"SDSS",        "band":"z"},
        "bU": {"instrument":"Bessel",      "band":"U"},
        "bB": {"instrument":"Bessel",      "band":"B"},
        "bV": {"instrument":"Bessel",      "band":"V"},
        "bR": {"instrument":"Bessel",      "band":"R"},
        "bI": {"instrument":"Bessel",      "band":"I"},
        "4g": {"instrument":"PTF 48-Inch", "band":"g"},
        "4r": {"instrument":"PTF 48-Inch", "band":"r"},
        "6g": {"instrument":"PTF 60-Inch", "band":"g"},
        "6r": {"instrument":"PTF 60-Inch", "band":"r"},
        "6i": {"instrument":"PTF 60-Inch", "band":"i"},
        "Uu": {"instrument":"UVOT",        "band":"U"},
        "Ub": {"instrument":"UVOT",        "band":"B"},
        "Uv": {"instrument":"UVOT",        "band":"V"},
        "Um": {"instrument":"UVOT",        "band":"M2"},
        "U1": {"instrument":"UVOT",        "band":"W1"},
        "U2": {"instrument":"UVOT",        "band":"W2"},
        "GN": {"instrument":"GALEX",       "band":"NUV"},
        "GF": {"instrument":"GALEX",       "band":"FUV"},
        "CR": {"instrument":"Clear",       "band":"r"  },
        "RO": {"instrument":"ROTSE"                    },
        "X1": {"instrument":"Chandra"                  },
        "X2": {"instrument":"XRT"                      },
        "Xs": {"instrument":"XRT",         "band":"soft"},
        "Xm": {"instrument":"XRT",         "band":"hard"},
        "XM": {"instrument":"XMM"                      }
    }
    for file in sorted(glob.glob("../tde-external/old-tdefit/*.dat"), key=lambda s: s.lower()):
        f = open(file,'r')
        tsvin = csv.reader(f, delimiter='\t', skipinitialspace=True)

        source = ''
        yrsmjdoffset = 0.
        for row in tsvin:
            if row[0] == 'name':
                name = re.sub('<[^<]+?>', '', row[1].split(',')[0].strip())
                name = add_event(name)
            elif row[0] == 'citations':
                citarr = row[1].split(',')
                for cite in citarr:
                    if '*' in cite:
                        source = get_source(name, reference = cite.strip())
            elif row[0] == 'nhcorr':
                hostnhcorr = True if row[1] == 'T' else False
            elif row[0] == 'restframe':
                restframe = True if row[1] == 'T' else False
            elif row[0] == 'yrsmjdoffset':
                yrsmjdoffset = float(row[1])
            if row[0] == 'redshift':
                redshift = float(row[1].split(',')[0].strip(' *'))

        f.seek(0)

        for row in tsvin:
            if row[0] == 'redshift':
                add_quanta(name, 'redshift', row[1], source)
            elif row[0] == 'host':
                add_quanta(name, 'host', row[1], source)
            elif row[0] == 'claimedtype':
                add_quanta(name, 'claimedtype', row[1], source)
            elif row[0] == 'citations':
                add_quanta(name, 'citations', row[1], source)
            elif row[0] == 'notes':
                add_quanta(name, 'notes', row[1], source)
            elif row[0] == 'nh':
                add_quanta(name, 'nh', row[1], source)
            elif row[0] == 'photometry':
                if yrsmjdoffset == 0.:
                    timeunit = row[1]
                    time = row[2]
                    lrestframe = restframe
                else:
                    timeunit = 'MJD'
                    if restframe:
                        # Currently presume only the time, not the flux, has been affected by redshifting.
                        time = str(yrsmjdoffset + float(row[2])*365.25*(1.0 + redshift))
                    else:
                        time = str(yrsmjdoffset + float(row[2])*365.25)
                    lrestframe = False
                instrument = ''
                iband = row[3]
                if iband in oldbanddict:
                    if 'band' in oldbanddict[iband]:
                        band = oldbanddict[iband]['band']
                    if 'instrument' in oldbanddict[iband]:
                        instrument = oldbanddict[iband]['instrument']
                else:
                    band = iband
                upperlimit = True if row[6] == '1' else False
                if 'X' in iband:
                    counts = row[4]
                    e_counts = row[5] if float(row[5]) != 0.0 else ''
                    add_photometry(name, time = time, timeunit = timeunit, band = band, counts = counts, e_counts = e_counts,
                            upperlimit = upperlimit, restframe = lrestframe, hostnhcorr = hostnhcorr, instrument = instrument, source = source)
                else:
                    magnitude = row[4]
                    e_magnitude = row[5] if float(row[5]) != 0.0 else ''
                    add_photometry(name, time = time, timeunit = timeunit, band = band, magnitude = magnitude, e_magnitude = e_magnitude,
                            upperlimit = upperlimit, restframe = lrestframe, hostnhcorr = hostnhcorr, instrument = instrument, source = source)

# Import primary data sources from Vizier
if do_task('vizier'):
    Vizier.ROW_LIMIT = -1
    # VizieR imports go here

    #journal_events()

if do_task('ogle'): 
    basenames = ['transients']
    oglenames = []
    ogleupdate = [True]
    for b, bn in enumerate(basenames):
        if args.update and not ogleupdate[b]:
            continue
        response = urllib.request.urlopen('http://ogle.astrouw.edu.pl/ogle4/' + bn + '/transients.html')
        soup = BeautifulSoup(response.read(), "html5lib")
        links = soup.findAll('a')
        breaks = soup.findAll('br')
        datalinks = []
        for a in links:
            if a.has_attr('href'):
                if '.dat' in a['href']:
                    datalinks.append('http://ogle.astrouw.edu.pl/ogle4/' + bn + '/' + a['href'])

        ec = -1
        reference = 'OGLE-IV Transient Detection System'
        refurl = 'http://ogle.astrouw.edu.pl/ogle4/transients/transients.html'
        for br in breaks:
            sibling = br.nextSibling
            if 'Ra,Dec=' in sibling:
                line = sibling.replace("\n", '').split('Ra,Dec=')
                name = line[0].strip()
                ec += 1

                if name in oglenames:
                    continue
                oglenames.append(name)

                mySibling = sibling.nextSibling
                atelref = ''
                claimedtype = ''
                while 'Ra,Dec=' not in mySibling:
                    if isinstance(mySibling, Tag):
                        atela = mySibling
                        if atela and atela.has_attr('href') and 'astronomerstelegram' in atela['href']:
                            atelref = atela.contents[0].strip()
                            atelurl = atela['href']
                            if 'TDE' in atela.contents[0]:
                                claimedtype = 'TDE'
                    mySibling = mySibling.nextSibling
                    if mySibling is None:
                        break

                if claimedtype != 'TDE':
                    continue
                name = add_event(name)

                nextSibling = sibling.nextSibling
                if isinstance(nextSibling, Tag) and nextSibling.has_attr('alt') and nextSibling.contents[0].strip() != 'NED':
                    radec = nextSibling.contents[0].strip().split()
                else:
                    radec = line[-1].split()
                ra = radec[0]
                dec = radec[1]
                lcresponse = urllib.request.urlopen(datalinks[ec])
                lcdat = lcresponse.read().decode('utf-8').splitlines()
                sources = [get_source(name, reference = reference, url = refurl)]
                if atelref and atelref != 'ATel#----':
                    sources.append(get_source(name, reference = atelref, url = atelurl))
                sources = ','.join(sources)

                if name[:4] == 'OGLE':
                    if name[4] == '-':
                        if is_number(name[5:9]):
                            add_quanta(name, 'discoveryear', name[5:9], sources)
                    else:
                        if is_number(name[4:6]):
                            add_quanta(name, 'discoveryear', '20' + name[4:6], sources)

                add_quanta(name, 'snra', ra, sources)
                add_quanta(name, 'sndec', dec, sources)
                if claimedtype and claimedtype != '-':
                    add_quanta(name, 'claimedtype', claimedtype, sources)
                elif 'SN' not in name and 'claimedtype' not in events[name]:
                    add_quanta(name, 'claimedtype', 'Candidate', sources)
                for row in lcdat:
                    row = row.split()
                    mjd = str(jd_to_mjd(Decimal(row[0])))
                    magnitude = row[1]
                    if float(magnitude) > 90.0:
                        continue
                    e_magnitude = row[2]
                    upperlimit = False
                    if e_magnitude == '-1' or float(e_magnitude) > 10.0:
                        e_magnitude = ''
                        upperlimit = True
                    add_photometry(name, time = mjd, band = 'I', magnitude = magnitude, e_magnitude = e_magnitude, source = sources, upperlimit = upperlimit)
        journal_events()

if do_task('writeevents'): 
    files = []
    for rep in repfolders:
        files += glob.glob('../' + rep + "/*.json")

    for fi in files:
        events = OrderedDict()
        name = os.path.basename(os.path.splitext(fi)[0])
        name = add_event(name)
        derive_and_sanitize()
        write_all_events(empty = True)

print("Memory used (MBs on Mac, GBs on Linux): " + "{:,}".format(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024./1024.))

