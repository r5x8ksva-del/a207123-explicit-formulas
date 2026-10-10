# -*- coding: utf-8 -*-
"""Replay the paper/guide part of a report patch on the committed versions (git HEAD) of paper/main.tex and
paper/reviewer_guide.tex, so that the files in the work tree are exactly what the patch script produces.

The script must define PAPER (and optionally PAPER_RE, GUIDE) and a function patch(path, reps, regex=()).
Usage (task C root):  py -3.14 code/main_extra/replay_paper_patch.py code/main_extra/report_patches/<patch>.py
"""
import importlib.util
import os
import subprocess
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def main(script):
    os.chdir(ROOT)
    for f in ['paper/main.tex', 'paper/reviewer_guide.tex']:
        data = subprocess.run(['git', 'show', 'HEAD:' + f], capture_output=True, check=True).stdout
        open(f, 'wb').write(data)
    spec = importlib.util.spec_from_file_location('patchmod', os.path.abspath(script))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    m.patch(os.path.join(ROOT, 'paper', 'main.tex'), m.PAPER, getattr(m, 'PAPER_RE', ()))
    if getattr(m, 'GUIDE', None):
        m.patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), m.GUIDE)


if __name__ == '__main__':
    main(sys.argv[1])
