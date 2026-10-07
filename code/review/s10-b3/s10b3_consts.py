# -*- coding: utf-8 -*-
"""s10-b3：报告里引用的几个浮点常数（只作示意；严格的界见 s10b3_fiber.py 的 F5 有理区间）。"""
import numpy as np
r = np.roots([1,0,1,-1]); xi = [z.real for z in r if abs(z.imag)<1e-12][0]; xi2=[z for z in r if z.imag>1e-12][0]
print("xi", xi, "xi2", xi2, "|xi2|^2*xi", abs(xi2)**2*xi)
print("2xi^3", 2*xi**3, "bound", xi**-1.5*(xi**-3-1))
rho=1/xi; print("rho^4(rho^2-1)", rho**4*(rho**2-1), "conj bound", abs(1/xi2)**4*(1+abs(1/xi2)**2))
print("v(3/2) for alpha=2beta, beta=1..3:", [(-27/4)**b for b in (1,2,3)])
