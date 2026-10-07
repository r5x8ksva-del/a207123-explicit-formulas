# -*- coding: utf-8 -*-
"""Check every DOI in the bibliography of paper/main.tex against Crossref (read-only, one request per DOI,
one second apart): the DOI must resolve, and the Crossref title, year, volume and first page must agree
with the \\bibitem text.

Usage:
  py -3.14 code/main_extra/check_bib_dois.py paper/main.tex      (exit code 1 on any FAIL; needs network)
"""
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

UA = 'check_bib_dois.py (read-only citation check)'


def norm(s):
    s = re.sub(r'\\[a-zA-Z]+', ' ', s)          # drop TeX commands
    s = s.replace('~', ' ').replace('{', ' ').replace('}', ' ')
    return ' '.join(re.findall(r'[a-z0-9]+', s.lower()))


def bibitems(tex):
    body = tex.split(r'\begin{thebibliography}', 1)[1].split(r'\end{thebibliography}', 1)[0]
    parts = re.split(r'\\bibitem\{([^}]*)\}', body)
    return {parts[i]: parts[i + 1].strip() for i in range(1, len(parts), 2)}


def crossref(doi):
    url = 'https://api.crossref.org/works/' + urllib.parse.quote(doi, safe='/')
    req = urllib.request.Request(url, headers={'User-Agent': UA})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)['message']


def years(msg):
    out = set()
    for key in ('issued', 'published-print', 'published-online', 'published'):
        for parts in (msg.get(key) or {}).get('date-parts') or []:
            if parts and parts[0]:
                out.add(int(parts[0]))
    return out


def main(path):
    tex = open(path, encoding='utf-8').read()
    items = bibitems(tex)
    nfail = npass = 0
    for key, text in items.items():
        m = re.search(r'\\url\{https://doi\.org/([^}]*)\}', text)
        if not m:
            print('---- %-14s no DOI' % key)
            continue
        doi = m.group(1)
        problems = []
        try:
            msg = crossref(doi)
        except urllib.error.HTTPError as e:
            msg, problems = None, ['Crossref HTTP %d' % e.code]
        except Exception as e:                      # network or JSON trouble counts as a failure
            msg, problems = None, ['Crossref error: %s' % e]
        if msg is not None:
            item = norm(text)
            title = norm(' '.join(msg.get('title') or []))
            words = [w for w in title.split() if len(w) >= 4]
            hit = sum(1 for w in words if w in item.split())
            if not words or hit < 0.8 * len(words):
                problems.append('title %r matches %d of %d words' % (title, hit, len(words)))
            ys = years(msg)
            if not any(str(y) in text or str(y + 1) in text or str(y - 1) in text for y in ys):
                problems.append('year %s not in item' % sorted(ys))
            vol = msg.get('volume')
            if vol:                                 # some publishers store e.g. 'Volume 17, Issue 1'
                vol = (re.findall(r'[0-9]+', vol) or [None])[0]
            if vol and not re.search(r'(?<![0-9])%s(?![0-9])' % re.escape(vol), text):
                problems.append('volume %s not in item' % vol)
            page = (msg.get('page') or '').split('-')[0]
            if page and page not in text:
                problems.append('first page %s not in item' % page)
            info = '%s | %s | vol %s | p %s' % (title[:60], sorted(ys), vol, msg.get('page'))
        else:
            info = ''
        if problems:
            nfail += 1
            print('FAIL %-14s %s  %s  %s' % (key, doi, '; '.join(problems), info))
        else:
            npass += 1
            print('PASS %-14s %s  %s' % (key, doi, info))
        time.sleep(1)
    print('%d PASS, %d FAIL' % (npass, nfail))
    return 1 if nfail else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else 'paper/main.tex'))
