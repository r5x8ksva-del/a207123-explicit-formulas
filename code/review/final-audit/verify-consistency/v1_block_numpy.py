# -*- coding: utf-8 -*-
"""#0 验证：屏蔽 numpy（sys.modules['numpy']=None 使 import numpy 抛 ImportError）后运行指定脚本。
用法：py -3.14 v1_block_numpy.py <script> [args...]（工作目录 = 脚本所在目录）"""
import sys, os, runpy
sys.modules['numpy'] = None
script = sys.argv[1]
sys.argv = [script] + sys.argv[2:]
sys.path.insert(0, os.path.dirname(os.path.abspath(script)))
runpy.run_path(script, run_name='__main__')
