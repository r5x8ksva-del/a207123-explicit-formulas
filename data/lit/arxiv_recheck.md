# arXiv 复查（2026-10-07 第二次，只读）

由 `code/novelty/arxiv_recheck.py` 从 `data/lit/raw_arxiv_recheck/` 生成。arXiv API 只检索元数据（题名、摘要、作者），不含全文。

| 查询 | 目的 | 排序 | 命中总数 | 取回 | 检索式 |
|---|---|---|---|---|---|
| new01 | 最新：Hardin 的表 | date | 374 | 50 | `all:Hardin` |
| new02 | 最新：OEIS 猜想的证明 | date | 96 | 96 | `abs:OEIS AND (abs:conjecture OR abs:conjectures OR abs:conjectured)` |
| new03 | 最新：0-1 数组/矩阵避开模式 | date | 37 | 37 | `(abs:"binary arrays" OR abs:"0-1 arrays" OR abs:"binary matrices" OR abs:"01-matrices") AND (abs:avoiding OR abs:pattern OR abs:patterns OR abs:forbidden)` |
| new04 | 最新：Stirling 型数与零化子/递推 | date | 16 | 16 | `abs:Stirling AND (abs:annihilator OR abs:annihilating OR abs:holonomic OR abs:"D-finite" OR abs:Ore)` |
| new05 | 最新：Stirling-like | date | 10 | 10 | `abs:"Stirling-like" OR abs:"Stirling like"` |
| new06 | 最新：非 D-finite 的二元序列 | date | 54 | 50 | `(abs:"not D-finite" OR abs:"non-D-finite" OR abs:"non-holonomic" OR abs:nonholonomic) AND abs:sequence` |
| new07 | 最新：AI/Lean 证 OEIS | date | 13 | 13 | `(abs:OEIS) AND (abs:Lean OR abs:"language model" OR abs:"language models" OR abs:LLM OR abs:AI)` |
| new08 | 最新：math.CO 里提到 OEIS 的 | date | 194 | 100 | `cat:math.CO AND abs:OEIS` |
| new09 | 最新：Kauers | date | 93 | 40 | `au:Kauers` |
| new10 | 最新：Koutschan | date | 75 | 30 | `au:Koutschan` |
| new11 | 最新：Dougherty-Bliss（下划线写法，0 命中，保留作记录） | date | 0 | 0 | `au:Dougherty_Bliss` |
| new11b | 最新：Dougherty-Bliss（拆开写法，0 命中，保留作记录） | date | 0 | 0 | `au:Dougherty AND au:Bliss` |
| new11c | 最新：Dougherty-Bliss | date | 18 | 18 | `au:"Dougherty-Bliss"` |
| x01 | 最新：二维模式避免（数组/矩阵） | date | 32 | 32 | `(abs:"pattern avoidance" OR abs:"pattern-avoiding" OR abs:"avoiding patterns") AND (abs:"two-dimensional" OR abs:arrays OR abs:matrices)` |
| x02 | 最新：zeta 多项式 | date | 22 | 22 | `abs:"zeta polynomial" OR abs:"zeta polynomials"` |
| x03 | T3.8/T3.9：Stirling 数的零化子 | relevance | 13 | 13 | `abs:Stirling AND (abs:annihilator OR abs:annihilators OR abs:"annihilating operator")` |
| x05_fried | 找 Fried 的 OEIS 猜想证明系列（第一种写法） | date | 4 | 4 | `au:Fried AND abs:OEIS` |
| x06_fried | 找 Fried 的 OEIS 猜想证明系列（补全） | date | 8 | 8 | `au:Fried AND (ti:conjectures OR ti:OEIS OR abs:"Integer Sequences")` |
| x04 | 最新：二进制数组的行列禁止模式 | date | 13 | 13 | `(abs:"rows and columns" OR abs:"each row" OR abs:"every row") AND (abs:forbidden OR abs:avoid OR abs:avoiding OR abs:avoids) AND (abs:binary OR abs:"0-1")` |
| new12 | 最新：Zeilberger | date | 269 | 40 | `au:Zeilberger` |
| t39a | T3.9：牛顿多边形与递推算子 | relevance | 28 | 28 | `abs:"Newton polygon" AND (abs:recurrence OR abs:annihilator OR abs:"Ore algebra" OR abs:operator)` |
| t39b | T3.9/T3.8：二元序列的零化理想由一条递推生成 | relevance | 4 | 4 | `(abs:annihilator OR abs:"annihilating ideal") AND (abs:bivariate OR abs:"two-dimensional" OR abs:"two variables") AND abs:recurrence` |
| t39c | T3.8：Ore 代数左理想、象限、饱和 | relevance | 1 | 1 | `abs:"Ore algebra" AND (abs:quadrant OR abs:saturation OR abs:contraction)` |
| t38a | T3.8：四项/三角递推的零化子分类 | relevance | 1 | 1 | `(abs:"triangular recurrence" OR abs:"triangle recurrence") AND (abs:annihilator OR abs:ideal OR abs:holonomic)` |
| t26a | T2.6：Stirling×二项式单和不存在 | relevance | 14 | 14 | `abs:Stirling AND (abs:"single sum" OR abs:"no closed form" OR abs:"closed form") AND abs:binomial` |
| t26b | T2.6：留数与范数证明不存在某类公式 | relevance | 79 | 30 | `(abs:residue OR abs:residues) AND abs:norm AND (abs:"generating function" OR abs:sum)` |
| t24a | T2.4：r-Stirling 与模式/词的计数 | relevance | 8 | 8 | `abs:"r-Stirling" AND (abs:words OR abs:patterns OR abs:sequences OR abs:arrays)` |
| t24b | T2.4：块分解计数高度序列 | relevance | 1 | 1 | `(abs:"height sequences" OR abs:"height sequence") AND (abs:Stirling OR abs:patterns OR abs:enumeration)` |
| t10a | T1.0：允许行偏序集与 zeta 多项式 | relevance | 0 | 0 | `abs:"zeta polynomial" AND (abs:words OR abs:arrays OR abs:matrices)` |
| t13a | T1.3：y^3=y^2+m、P_m 型分母 | relevance | 16 | 16 | `(abs:"1-x-mx^3" OR abs:"x^3=x^2+m" OR abs:"y^3=y^2+m") OR (abs:Narayana AND abs:generalized AND abs:recurrence)` |
| t41a | T4.1：三角的近对角线是多项式 | relevance | 31 | 30 | `(abs:"near-diagonal" OR abs:"near diagonal" OR abs:subdiagonal OR abs:diagonals) AND abs:polynomial AND (abs:Stirling OR abs:triangle)` |
| t29a | T1.9：OEIS 列递推（Barker 猜想）被证明 | relevance | 0 | 0 | `abs:Barker AND abs:OEIS` |

## 全部取回的文章（626 篇，按首次提交日期倒序）

| arXiv | 提交 | 题名 | 作者 | 命中的查询 |
|---|---|---|---|---|
| 2610.05776v1 | 2026-10-05 | On three conjectures of Kimberling concerning the array $\lfloor k\varphi^n\rfloor$ | Alex Ashburn | new02 new08 |
| 2610.04150v1 | 2026-10-02 | Hurwitz Stability of Generalized Turán Expressions of Polynomial Sequences | Huihua Gao, Xin-Bei Liu | t13a |
| 2610.03111v1 | 2026-10-02 | Binomial expansions of Jacobi-Stirling numbers and real-rootedness of Jacobi-Stirling descent polynomials | Shi-Mei Ma, Ming-Xin Wang | t41a |
| 2610.00775v1 | 2026-09-30 | Riordan Arrays and Shifted Hankel Determinants of OEIS A005773 | Daniel Yaqubi, Madjid Mirzavaziri | new08 |
| 2609.37592v2 | 2026-09-29 | Quantum Statistical Thermal Engine at the BCS-BEC crossover | Santiago Henríquez Lira, Felipe Isaule, Martín HvE Groves, Francisco J. Peña 等 | new05 |
| 2609.38084v1 | 2026-09-29 | Peaks and peak-nestings on unit interval graphs | Per Alexandersson, Leonardo Saud Maia Leite | new08 |
| 2609.32264v1 | 2026-09-26 | LANTERN: Illuminating Hidden Mathematical Knowledge in Language Models | Pavel Tikhonov, Elena Tutubalina, Ivan Oseledets, Dmitry I. Ignatov 等 | new07 |
| 2609.31189v1 | 2026-09-25 | Differential Recursions, Projective Discriminants, and Algebraic Generating Functions | S. Voloshyn | new02 |
| 2609.28892v1 | 2026-09-24 | Trident Tableaux for Tree-Child Networks with One Reticulation Node: A Bijection with Two-Wall Tableaux | Hexuan Liu | new08 |
| 2609.30350v1 | 2026-09-24 | Combinatorial aspects of the Delannoy Lattice | Xi Chen, Yuxian Dong | x02 |
| 2609.28650v1 | 2026-09-23 | A parking function analog of the Schröder numbers | Lucy Martinez, Doron Zeilberger | new12 |
| 2609.26965v1 | 2026-09-22 | Tension between MiniBooNE and MicroBooNE within a 3+1 Sterile Neutrino Framework using Simulation-Based Inference | Julia P. Woodward, Austin Schneider, Joshua Villarreal, John Hardin 等 | new01 |
| 2609.26775v1 | 2026-09-22 | Optical Ion Clock with Engineered Immunity to Motion-Induced Frequency Shifts | Mark Lide, Wesley Hardin, Christian Sanner | new01 |
| 2609.28512v1 | 2026-09-21 | Counterexamples to a conjecture of Kamenetsky on OEIS A173419 | Rosario Patanè | new02 |
| 2609.25098v1 | 2026-09-19 | Approximating Pi (and other constants) by Radicals in the Footsteps of Rabbi Abraham Ibn Ezra and Guru RSJ Reddy | Doron Zeilberger | new12 |
| 2609.19895v1 | 2026-09-17 | Fractal Hyper-Trees: Combinatorial Enumeration, Symmetry Properties, and Ultrametric Structures | Jean-Jacques Salone | new08 |
| 2609.18237v2 | 2026-09-16 | The 3/4 Conjecture for q-Ary Fix-Free Codes With at Most Three Distinct Codeword Lengths | Weiguo Gao, Zhi Shan | x04 |
| 2609.13915v1 | 2026-09-12 | Invariant Algebras of Low-Rank Neutrino Matter Flows: Krylov-Plücker Invariants, the $3+1$ Toric Ring, and Controlled Deformations | Jianlong Lu | t41a |
| 2609.12055v1 | 2026-09-10 | Time-Integrated Searches for Sub-TeV Neutrino Sources with IceCube-DeepCore | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2609.10931v1 | 2026-09-10 | IceCube neutrino point-source searches in the direction of the KM3NeT ultra-high-energy event | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2609.10492v1 | 2026-09-09 | The Distribution of Double Deficiencies in Pattern-Avoiding Permutations | Tipaluck Krityakierne, Thotsaporn Aek Thanatipanonda, Doron Zeilberger | new12 |
| 2609.08562v1 | 2026-09-08 | Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples | Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian | new08 |
| 2609.07325v1 | 2026-09-07 | Real-rooted Eulerian polynomials from permutations, words, and paths | Per Alexandersson | new02 new08 |
| 2609.07238v1 | 2026-09-07 | A Proof of Bala's Congruence Conjectures for A158690 | Ahaan Kallat | new02 new08 |
| 2609.02220v1 | 2026-09-02 | Recurrences for permutations with long increasing subsequences | Manuel Kauers, Chen Wang | new06 new09 |
| 2609.00657v1 | 2026-09-01 | Search for Neutrinos from Tidal Disruption Events with IceCube | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2609.01690v1 | 2026-09-01 | Iterated-sumset spectra: The complete exponent law and its rank geometry | Henry Shin | new02 new08 |
| 2608.29746v1 | 2026-08-30 | Searching for Extra Dimensions and Copies of the Standard Model with IceCube | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2608.29555v1 | 2026-08-30 | Truncations of the ring of number-theoretic functions, revisited | Jan Snellman | new02 |
| 2608.29741v1 | 2026-08-30 | Wallis-type products with polynomial exponents and the Dirichlet beta function at negative integers | Joshua W. E. Farrell | new08 |
| 2608.29411v1 | 2026-08-29 | Where Induction Runs Out: Description-Length Difficulty and the Memorisation Gap in Integer-Sequence Benchmarks | Sabilashan Ganeshan | new07 |
| 2608.28395v1 | 2026-08-28 | Astrophysical Sensitivity Projections for the IceCube Upgrade | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2608.27583v1 | 2026-08-27 | Enumerating separable derangements | Robert Dougherty-Bliss, Alejandro B. Galván, Michaela A. Polley, David Shuster | new11c |
| 2609.29503v1 | 2026-08-24 | A micromorphic constitutive framework for (non)linear softening modeling | Rafael Abreu | new01 |
| 2608.22596v1 | 2026-08-23 | Charmonia at Finite Momentum and Spatial Correlators in Quark-Gluon Plasma | Thomas Hardin, Ralf Rapp | new01 |
| 2608.22053v2 | 2026-08-22 | An application of Jacobi's residue formula and proofs of some other conjectures on binomial coefficients | Rohun Easwar | new02 new08 |
| 2608.20579v1 | 2026-08-20 | Estimating Many Constants With a Coin | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2608.18801v1 | 2026-08-19 | A revised framework for the assessment of psychological safety in autonomous vehicles | Yandika Sirgabsou, Benjamin Hardin, François Leblanc, Efi Raili 等 | new01 |
| 2608.18778v1 | 2026-08-19 | Engineering Psychological Safety in Autonomous Vehicles: A Systems-Theoretic Framework for Psychological Safety in Autonomous Vehicles and its Validation in Real-World Scenarios | Yandika Sirgabsou, Benjamin Hardin, François Leblanc, Efi Raili 等 | new01 |
| 2608.18380v1 | 2026-08-18 | Direction-Adaptive Plane-Wave Discontinuous Galerkin Methods for the Helmholtz Equation | Shelvean Kapita | t26b |
| 2608.15415v2 | 2026-08-15 | Positive quasimodular forms and the sign uncertainty principle | Seewoo Lee | new01 |
| 2608.15322v1 | 2026-08-15 | Iterative State- and Control-Dependent Model Predictive Control: A Jacobian-Free Formulation for Constrained Nonlinear Systems | Mohammadreza Kamaldar | new06 |
| 2608.13899v2 | 2026-08-14 | Does the Hardin-Taylor Predictor Actually Predict the Future? Yes; but Only in Retrospect | Ulvi Yurtsever | new01 |
| 2608.11941v2 | 2026-08-12 | OEIS Open: How many conjectures can language models turn into theorems? | Tom Adamczewski | new02 new07 |
| 2608.12250v2 | 2026-08-12 | From Whole-Space Theory to Boundary Value Problems for Mixed-Order PDEs | Guillaume Neuttiens, Jonas Sauer | t39a |
| 2608.07801v2 | 2026-08-07 | Integrating spectral and morphological plant features with decision-tree models for early-season cotton biomass and nitrogen status estimation from multi-year UAV data | Vaishali Swaminathan, Nithya Rajan, J Alex Thomasson, Amrit Shrestha 等 | new01 |
| 2608.06543v1 | 2026-08-06 | Estimating the sensitivity of the IceCube Upgrade to probe the interior of the Earth using atmospheric neutrino oscillations |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2608.02550v2 | 2026-08-03 | A Joint Bayesian Boolean Matrix Factorization with Application to Chromosomal Copy Number Alterations in Multiple Myeloma | Adolphus Wagala, Samur Mehmet, Giovanni Parmigiani | new03 |
| 2607.29369v2 | 2026-07-31 | Automatic Enumeration of Tilings by Polyominoes | Lucy Martinez | new08 |
| 2607.26613v1 | 2026-07-29 | On a Question of Lehmer concerning the Comtet Numbers | Sangtae Jeong | new02 new08 |
| 2609.25011v1 | 2026-07-29 | A Kernel-Certified Verification of the Erdős-Mollin-Walsh Conjecture below $10^{14}$ | Ibrahim Mian, Shayaan Siddique | new02 new07 |
| 2607.27003v1 | 2026-07-29 | Algorithms for Linear Ordinary Differential Operators | Jean Della Dora, Stephen M. Watt | t39a |
| 2607.25966v1 | 2026-07-28 | High-energy neutrino emission from the Milky Way | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2607.26334v1 | 2026-07-28 | The Combinatorics of Multi-Lane Merging | Aurora Hiveley, Doron Zeilberger | new12 |
| 2607.26048v1 | 2026-07-28 | Isotropic Decompositions via Inverse Eigenvectors | Gergely Ambrus | t26b |
| 2607.22202v1 | 2026-07-24 | Mersenne Representation, the Conolly Sequence, and Soliton Profiles over Finite Fields | Fumitaka Yura | new02 new08 |
| 2607.24832v1 | 2026-07-23 | Further proofs of conjectures from the OEIS | Sela Fried | new02 x05_fried x06_fried |
| 2607.20299v1 | 2026-07-22 | On (3,1)-regular graphs with one more vertex than edges | Frédéric Chyzak, Hui Huang, Manuel Kauers | new08 new09 |
| 2607.19844v2 | 2026-07-22 | Binomial probabilities at a fixed distance from the mode: size-biasing and the complete asymptotic expansion | Neven Elezović | t26a |
| 2607.18313v1 | 2026-07-17 | A Proof of Bala's Congruence Conjecture for A028342 | Ahaan Kallat | new02 new08 |
| 2607.15894v1 | 2026-07-17 | The minimum surface area of $k$ unequal boxes tiling a cube: sharp thresholds, a fault-free law, and a reduction to two dimensions | Diego Lago Gómez | new08 |
| 2607.14887v1 | 2026-07-16 | Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series | Xinru Jiang, Suzhen Wen, Yueming Zhong | t41a |
| 2607.12026v1 | 2026-07-13 | Learning the Graphical Nature of Symmetries | Rashid Barket, Enrico Grimaldi, Yacoub Hendi, Edward Hirst 等 | new02 new08 |
| 2607.10778v2 | 2026-07-12 | The Arithmetic of Semirings Part I: Ideals | Jay Chen, Trevor Hyde, Dorien Laurens, Jasper Piermarini 等 | t39a |
| 2607.08049v1 | 2026-07-09 | A set of points on the sphere with small Riesz energy | Stefan Steinerberger | new01 |
| 2607.05431v1 | 2026-07-03 | A quick proof that $321$-avoiding permutations without double deficiencies are counted by the Motzkin numbers | Tipaluck Krityakierne, Thotsaporn "Aek" Thanatipanonda, Doron Zeilberger | new12 |
| 2607.02770v2 | 2026-07-02 | Gemma 4 Technical Report |  Gemma Team, Sherif El Abd, Vaibhav Aggarwal, Robin Algayres 等 | new01 |
| 2607.02644v2 | 2026-07-02 | High-Energy Neutrino Tomography of the Earth's Interior with IceCube |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2607.02078v2 | 2026-07-02 | WavePID: Low-energy flavor identification using single-PMT time series in IceCube |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2607.02613v1 | 2026-07-01 | Counting Unlabeled Chordal Graphs by Equivariant Evaporation | Matthew Sun | new08 |
| 2607.00651v1 | 2026-07-01 | On the number of extension closed additive subcategories for uniformly oriented $A_n$ quivers | Volodymyr Mazorchuk | new08 |
| 2606.31526v1 | 2026-06-30 | The number of labeled partial orders and topologies on 19 points | Rafael Ayala | new08 |
| 2606.30232v1 | 2026-06-29 | Structured Solutions of Prime-Base Binomial Congruences | Gabriel Araújo Guedes, Ricardo Nunes Machado Junior | new02 new08 |
| 2606.29838v1 | 2026-06-29 | Poisson-shot-noise hybrid machines: efficiency and quasistatic divergence | Rita Majumdar, Costantino Di Bello, Ralf Metzler, Rahul Marathe 等 | new05 |
| 2606.25905v2 | 2026-06-24 | SurgAtlas: A Large-Scale Surgical Video-Language Dataset with 2,391 Hours of Open and Minimally Invasive Surgery | Filippos Bellos, Andre S. Gala-Garza, Miaowei Wang, Alyssa M. Hardin 等 | new01 |
| 2606.26035v1 | 2026-06-24 | Every Nonnegative Integer Is a Sum of a Triangular, a Pentagonal, and a Heptagonal Number | Yichuan Cao, Dakai Guo, Ruichen Qiu, Ruyong Feng 等 | new02 new07 |
| 2606.22997v1 | 2026-06-22 | A Greatest Common Divisor Criterion of Certain Binomial Coefficients | Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng 等 | new02 new07 |
| 2606.22636v2 | 2026-06-21 | Spectral Gap for the Binary Fixed-Margin Swap Chain | Weibo Fu, Qian Qin, Guanyang Wang | new03 x04 |
| 2606.21432v1 | 2026-06-19 | Soliton-like Waves in a Two-Dimensional Recurrent Spiking Neural Network with Weighted Spike-Timing-Dependent Plasticity | Ch. Meessen | t39b |
| 2606.17491v2 | 2026-06-16 | A Bayesian Boolean Matrix Factorization with Application to Copy Number Analysis in Cancer | Adolphus Wagala, Mehmet Samur, Giovanni Parmigiani | new03 |
| 2606.13762v1 | 2026-06-11 | IceCube Real-time Searches for High-energy Neutrinos Coincident with LIGO/Virgo/KAGRA Gravitational-Wave Alerts in O4a |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2606.09321v2 | 2026-06-08 | Proof of Conjecture 19 of Ballantine, Beck, Merca, and Sagan on Elementary Symmetric Partitions | Arnav Garg | new02 new08 |
| 2606.09913v1 | 2026-06-06 | Proofs of several OEIS conjectures on determinants and permanents | Sela Fried | x06_fried |
| 2606.04989v1 | 2026-06-03 | What Can Eye Gaze Teach Us About Real-World Cycling? Insights From the Oxford RobotCycle Project | Benjamin Hardin, Efimia Panagiotaki, Daniele De Martini, Lars Kunze | new01 |
| 2606.05439v1 | 2026-06-03 | In How Many Ways can a Rectangle be Rectangled? | Pablo Blanco, Robert Dougherty-Bliss, Natalya Ter-Saakov, Doron Zeilberger | new11c new12 |
| 2606.04016v1 | 2026-05-31 | Witness-split + window-cardinality refinement for $r_3(N)$: Architecture, empirical results, and a structural hard pocket | Mehmet Ergezer | new02 new07 |
| 2606.01378v1 | 2026-05-31 | A Koopman Set-Membership Approach for Nonlinear Data-Driven Control with Stability Guarantees | Yifan Xie, Zuxun Xiong, Julian Berberich, Antonis Papachristodoulou 等 | t26b |
| 2605.30436v1 | 2026-05-28 | JWST Predictions for $z > 10$ Galaxies from the Renaissance Simulations -- I: Photometry and Sizes | Samantha E Hardin, John H Wise, Emily K Troutman | new01 |
| 2605.26792v1 | 2026-05-26 | Absorbing States of Binary Trust Gossip Are Counted by Plane Partitions | Nicholas Boichuk | new08 |
| 2605.26916v1 | 2026-05-26 | Polytopes and posets associated to preorders | Frédéric Chapoton, Christos A. Athanasiadis | x02 |
| 2605.26846v5 | 2026-05-26 | Signed Generalized Stirling Polynomials, Nested Sums, and Hyperbolic Secant Integral Identities | Abdulhafeez A. Abdulsalam, Michael J. Schlosser | t26a |
| 2605.22763v2 | 2026-05-21 | Advancing Mathematics Research with AI-Driven Formal Proof Search | George Tsoukalas, Anton Kovsharov, Sergey Shirobokov, Anja Surina 等 | new02 new07 |
| 2605.21529v6 | 2026-05-19 | A Matrix-Theoretic Exact Formula for Counting Primes in Intervals Between Consecutive Odd Squares | Wujie Shi | new02 new08 |
| 2605.19040v1 | 2026-05-18 | IceCube Second Track Data Release IceTracks-DR2: Data from 2008-2022 for Neutrino Source Searches | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2606.26110v1 | 2026-05-17 | Unified Nilpotent Operational Framework: Foundations, Algebraic Exactness, and Complexity | Ramon Moya | new04 |
| 2605.16553v1 | 2026-05-15 | An explicit algebraic generating function for OEIS A348410 | Tong Niu | new02 new06 new08 |
| 2605.15500v1 | 2026-05-15 | Three short proofs of Mathar's 2014 conjecture for OEIS A002627 | Tong Niu | new02 new08 |
| 2605.14213v1 | 2026-05-14 | A short proof of Mathar's 2013 recurrence conjecture for the reversible-binary-string sequence A032123 | Tong Niu | new02 new08 |
| 2605.15352v1 | 2026-05-14 | Diffusion Policy for Coordinated Control of a Nonholonomic Mobile Base and Dual Arms in Door Opening and Passing | Shangqun Yu, Matthew En, Daniel Wu, Sangjun Park 等 | new06 |
| 2605.12839v2 | 2026-05-13 | A short proof of Mathar's 2021 recurrence conjecture for the Lehmer-Comtet diagonal A045406 | Tong Niu | new02 new08 t41a |
| 2605.13666v1 | 2026-05-13 | When Does the Dice Sum Become Prime? | Christoph Koutschan, Tipaluck Krityakierne, Thotsaporn Aek Thanatipanonda | new10 |
| 2605.11351v1 | 2026-05-12 | A short proof of Mathar's 2020 recurrence conjecture for the generalized-Stirling sequence A001711 | Tong Niu | new02 new08 t41a |
| 2605.11137v2 | 2026-05-11 | The alternating compositions of weighted differential operators yield the weights' Wronskian with which constant? | Kian C. Shah, Arthemy V. Kiselev | new02 new08 |
| 2605.09683v3 | 2026-05-10 | Rook theory, normal ordering in the $q$-deformed Ore algebra and the polynomial generalization | Matthias Schork | new04 |
| 2605.08968v1 | 2026-05-09 | Proofs of four generating function conjectures for arbor polytopes | Feihu Liu, Jinlong Tang | x02 |
| 2605.08444v1 | 2026-05-08 | A short proof of Mathar's 2013 recurrence conjecture for the Laguerre sequence~A025166 | Tong Niu | new02 new08 |
| 2605.06600v1 | 2026-05-07 | Sensitivity Projections for Low-Mass Dark Matter Annihilation with the IceCube Upgrade | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2605.04369v1 | 2026-05-06 | A short proof of Mathar's 2016 recurrence conjecture for OEIS A176677 | Tong Niu | new02 new08 |
| 2605.04006v1 | 2026-05-05 | Saddle-Point Asymptotics for Chromatic and Tutte Polynomial Evaluations of Complete Multipartite Graphs | Zhiyang Sun | new02 new08 |
| 2605.03473v1 | 2026-05-05 | Polynomials from tilings of rectangles | John Ahlberg, Per Alexandersson | new08 |
| 2605.03170v2 | 2026-05-04 | A short proof of Mathar's 2013 recurrence conjecture for the Meixner sequence A214615 | Tong Niu | new02 new08 |
| 2605.01942v1 | 2026-05-03 | Combinatorial Analysis of Dyadic and Quasi-Dyadic Codes | Anthony Gómez-Fonseca, Gretchen L. Matthews, Kirsten D. Morris, Tefjol Pllaha | new03 |
| 2605.01637v1 | 2026-05-02 | The Banach-Butterfly Invariant: Influence-Adaptive Walsh Geometry for Ternary Polynomial Threshold Functions | Gorgi Pavlov | new07 new08 |
| 2604.25731v1 | 2026-04-28 | Enumerating Multi-Operator Monomials in Commutative and Noncommutative Settings | Yu Hin Au, Murray R. Bremner | t13a |
| 2604.24567v1 | 2026-04-27 | A correction adaptive two-grid finite element method for nonselfadjoint or indefinite elliptic problems | Fei Li, Qingguo Hong, Ming Tang, Liuqiang Zhong | t26b |
| 2604.23206v2 | 2026-04-25 | A Proof of Bala's General-$m$ Representation of the Harmonic Numbers | Tong Niu | new02 new08 |
| 2604.22668v2 | 2026-04-24 | Penalised and constrained geodesics in geometric control theory | Rufus Lawrence, Aleš Wodecki, Johannes Aspman, Jakub Mareček | new06 |
| 2604.19846v1 | 2026-04-21 | Neural posterior estimation of the neutrino direction in IceCube using transformer-encoded normalizing flows on the sphere | R. Abbasi, M. Ackermann, J. Adams, J. A. Aguilar 等 | new01 |
| 2604.03680v1 | 2026-04-04 | Separating zeros of polynomials using an added interlacing point | Kerstin Jordaan, Vikash Kumar | t13a |
| 2604.01956v1 | 2026-04-02 | Receding-Horizon Nonlinear Optimal Control With Safety Constraints Using Constrained Approximate Dynamic Programming | Ricardo Gutierrez, Jesse B. Hoagg | new06 |
| 2604.02542v1 | 2026-04-02 | Cascade-free sequences, dispersion index, and state avoidance for stateful digit-wise operations | Daniel Andreas Moj | new08 |
| 2604.00490v1 | 2026-04-01 | Incremental stability in $p=1$ and $p=\infty$: classification and synthesis | Simon Kuang, Xinfan Lin | t26b |
| 2603.25528v2 | 2026-03-26 | On separable permutations and three other pairs in the Schröder class | Juan B. Gil, Oscar A. Lopez, Michael D. Weiner | x01 |
| 2603.24315v1 | 2026-03-25 | Counting (and Randomly Generating) Hamiltonian Cycles in Rectangular Grids | Pablo Blanco, Doron Zeilberger | new12 |
| 2603.17287v1 | 2026-03-18 | Forest webs and pattern avoidance | Jessica Striker, Bridget Eileen Tenner | new08 |
| 2603.15322v1 | 2026-03-16 | A Simulation-Based Inference Evaluation of Tension Between MicroBooNE and MiniBooNE Results in a 3+1 Sterile Neutrino Global Fit | Julia P. Woodward, Joshua Villarreal, John M. Hardin, Austin Schneider 等 | new01 |
| 2603.15830v2 | 2026-03-16 | Necklaces, subset sums, and cyclic permutations | Robert Dougherty-Bliss, Sergi Elizalde | new11c |
| 2603.09939v2 | 2026-03-10 | The Hofstadter consecutive-sum sequence omits infinitely many positive integers | Quanyu Tang | new02 new08 |
| 2603.09003v2 | 2026-03-09 | High-optical-depth, sub-Doppler-width absorption lines at telecom wavelengths in hot, optically driven rubidium vapor | Inna Kviatkovsky, Lucas Pache, Viola-Antonella Zeilberger, Philipp Schneeweiss 等 | new12 |
| 2603.04229v1 | 2026-03-04 | p^(k)-Fibonacci Numbers of the p-Bratteli Diagram for Every Odd Prime p and Integer k>=0 | M. Parvathi, A. Tamilselvi, D. Hepsi | new08 |
| 2602.24155v1 | 2026-02-27 | Newton strata realization for hypersurfaces via explicit p-adic cohomology | Ryan Batubara, Jack J Garzella, Yongyuan Huang, Maximus Mellberg | t39a |
| 2602.22079v1 | 2026-02-25 | Overlap Zoo Beta: A Catalogue of ~800 Occulting Pairs in the DESI Legacy Survey using Citizen Science | T. Butrum, B. Holwerda, W. C. Keel, C. Robertson 等 | new01 |
| 2602.19255v1 | 2026-02-22 | Statistical Analysis of Hairpins and BasePairs in RNA Secondary Structures | AJ Bu, Manuel Kauers, Doron Zeilberger | new09 new12 |
| 2602.15208v2 | 2026-02-16 | Self-Convolutions of Generalized Narayana Numbers | Greg Dresden, Yuechen Xiao, Guanzhang Zhou | t13a |
| 2602.11041v3 | 2026-02-11 | Exploiting the Structure in Tensor Decompositions for Matrix Multiplication | Manuel Kauers, Jakob Moosbauer, Isaac Wood | new09 |
| 2602.11355v5 | 2026-02-11 | Boolean-Narayana numbers | Miklos Bona | t13a |
| 2602.10208v2 | 2026-02-10 | Evidence for neutrino emission from X-ray Bright Seyfert Galaxies in the Southern Hemisphere using Enhanced Starting Track Events with IceCube | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2602.09714v1 | 2026-02-10 | Fast Motion Planning for Non-Holonomic Mobile Robots via a Rectangular Corridor Representation of Structured Environments | Alejandro Gonzalez-Garcia, Sebastiaan Wyns, Sonia De Santis, Jan Swevers 等 | new06 |
| 2602.10005v2 | 2026-02-10 | Systematic Enumeration of Fundamental Quantities Involving Runs in Binary Strings | Félix Balado, Guénolé C. M. Silvestre | new08 |
| 2602.09261v4 | 2026-02-09 | Fibre-Product Stability, Kummer Gluing, and Composita for Universal Koszulity | Marina Palaisti | t26b |
| 2602.06873v1 | 2026-02-06 | Symbolic Integration in Weierstrass-like Extensions | Shaoshi Chen, Manuel Kauers, Wenqiao Li, Xiuyun Li 等 | new09 |
| 2601.22413v3 | 2026-01-29 | The Riemann Hypothesis through the looking of partitions | Carlos Segovia | new02 |
| 2601.16626v1 | 2026-01-23 | On generalized eigenvalues of MAX matrices to MIN matrices and of LCM matrices to GCD matrices | Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, Timo Tossavainen | new02 |
| 2601.12644v2 | 2026-01-19 | On Some Properties of Matrices with Entries Defined by Products of $k$-Fibonacci and $k$-Lucas Numbers | Pedro Fernando Fernández Espinosa, Maritza Liliana Arciniegas Torres, Camilo Andrés Acevedo Cadena | new08 |
| 2601.11757v1 | 2026-01-16 | Sequencelib: A Computational Platform for Formalizing the OEIS in Lean | Walter Moreira, Joe Stubbs | new07 |
| 2601.07595v3 | 2026-01-12 | Deep Search for Joint Sources of Gravitational Waves and High-Energy Neutrinos with IceCube During the Third Observing Run of LIGO and Virgo |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2601.07938v1 | 2026-01-12 | The genesis sequence, tree records and endofunctions | Enrica Duchi, Adrián Lillo, Pablo Puerto, Mercedes Rosas 等 | new08 |
| 2512.25037v1 | 2025-12-31 | Universal polar dual pairs of spherical codes found in $E_8$ and $Λ_{24}$ | S. V. Borodachov, P. G. Boyvalenkov, P. D. Dragnev, D. P. Hardin 等 | new01 |
| 2512.21785v1 | 2025-12-25 | Computing the 4D Geode | Dean Rubine | new08 |
| 2512.21319v1 | 2025-12-24 | Variationally correct operator learning: Reduced basis neural operator with a posteriori error estimation | Yuan Qiu, Wolfgang Dahmen, Peng Chen | t26b |
| 2512.17760v1 | 2025-12-19 | Constraining the Prompt Atmospheric Neutrino Flux Combining IceCube's Cascade and Track Samples | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2512.16562v1 | 2025-12-18 | Prompt Searches for Very-High-Energy γ-Ray Counterparts to IceCube Astrophysical Neutrino Alerts | J. Abhir, A. Biland, K. Brand, T. Bretz 等 | new01 |
| 2512.14856v2 | 2025-12-16 | T5Gemma 2: Seeing, Reading, and Understanding Longer | Biao Zhang, Paul Suganthan, Gaël Liu, Ilya Philippov 等 | new01 |
| 2512.13183v2 | 2025-12-15 | Efficient Path Generation with Curvature Guarantees by Mollification | Alfredo González-Calvin, Juan F. Jiménez, Héctor García de Marina | new06 |
| 2512.12274v2 | 2025-12-13 | Forbidden Induced Subgraph Characterization of Word-Representable Co-bipartite Graphs | Eshwar Srinivasan, Ramesh Hariharasubramanian | new03 |
| 2512.08686v1 | 2025-12-09 | On the Number of Posets | Rico Zöllner, Konrad Handrich | new08 |
| 2512.07803v1 | 2025-12-08 | How many coin tosses would you need until you get $n$ Heads or $m$ Tails? | Svante Janson, Lucy Martinez, Doron Zeilberger | new12 |
| 2512.07120v1 | 2025-12-08 | Chromatic Feature Vectors for 2-Trees: Exact Formulas for Partition Enumeration with Network Applications | J. Allagan, G. Morgan, S. Langley, R. Lopez-Bonilla 等 | t26a |
| 2512.06980v1 | 2025-12-07 | Bell Numbers and Stirling Numbers of the Mycielskian of Trees | J. Allagan, G. Morgan, D. Sinclair | new08 |
| 2512.05784v1 | 2025-12-05 | Machine Learning-Informed 3+1 Sterile Neutrino Global Fits using Posterior Density Estimation of Electron Disappearance Data | Joshua Villarreal, Julia Woodward, John Hardin, Janet Conrad | new01 |
| 2512.00416v1 | 2025-11-29 | Normal Ordering in the Algebra Generated by $x$ and $\mathrm{I}$ and a Combinatorial Generalization of Bessel Numbers | Abdelhay Benmoussa | new08 |
| 2511.22338v1 | 2025-11-27 | Nonholonomic Narrow Dead-End Escape with Deep Reinforcement Learning | Denghan Xiong, Yanzhe Zhao, Yutong Chen, Zichun Wang | new06 |
| 2511.21969v1 | 2025-11-26 | ZipperChain: Transmuting Trusted Third-Party Services Into Trustless Atomic Broadcast | Matteo Bjornsson, Taylor Hardin, Taylor Heinecke, Marcin Furtak 等 | new01 |
| 2511.19385v1 | 2025-11-24 | Limits on GeV-scale WIMP Annihilation in Dwarf Spheroidals with IceCube DeepCore | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2511.18905v2 | 2025-11-24 | Congruences Modulo Powers of 7 for the Reciprocal Crank Parity Function | Dandan Chen | new08 |
| 2511.16624v2 | 2025-11-20 | SAM 3D: 3Dfy Anything in Images |  SAM 3D Team, Xingyu Chen, Fu-Jen Chu, Pierre Gleize 等 | new01 |
| 2511.15920v1 | 2025-11-19 | Schubert Polynomials and Elementary Symmetric Products | Oma Makhija | x01 |
| 2511.12587v1 | 2025-11-16 | Explicit M-Polynomial and Degree-Based Topological Indices of Generalized Hanoi Graphs | El-Mehdi Mehiri | t41a |
| 2511.12329v1 | 2025-11-15 | Target Defense against Sequentially Arriving Intruders: Algorithm for Agents with Dubins Dynamics | Arman Pourghorban, Dipankar Maity | new06 |
| 2511.07314v3 | 2025-11-10 | The free bifibration on a functor | Bryce Clarke, Gabriel Scherer, Noam Zeilberger | new12 |
| 2511.06118v4 | 2025-11-08 | Growing Avoiders from the Right: An Operator-Theoretic Approach | Reza Rastegar | x01 |
| 2511.02121v1 | 2025-11-03 | On the integrality of some P-recursive sequences | Anastasia Matveeva | new06 |
| 2511.00918v2 | 2025-11-02 | Search for GeV-scale Dark Matter from the Galactic Center with IceCube-DeepCore |  The IceCube Collaboration, R. Abbasi, M. Ackermann, J. Adams 等 | new01 |
| 2510.26936v1 | 2025-10-30 | Comparing the numbers of subforests and subgraph-degree-tuples | Sergei Shteiner, Pavel Shteyner | new02 new08 |
| 2510.24957v1 | 2025-10-28 | Characterization of the Three-Flavor Composition of Cosmic Neutrinos with IceCube | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2510.22584v5 | 2025-10-26 | Regular triangle unions with maximal number of sides | Giedrius Alkauskas | new08 |
| 2510.22078v1 | 2025-10-24 | Some 2-adic integers related to the odd part of 2^e! | Donald M. Davis | new02 |
| 2510.21056v1 | 2025-10-24 | On the Number of Exceptional Pairs Over a Class of Nakayama Algebras | Pedro Fernando Fernández Espinosa, David Reynoso-Mercado | new08 |
| 2510.21172v1 | 2025-10-24 | A Unified Matrix Factorization Framework for Classical and Robust Clustering | Angshul Majumdar | t26b |
| 2510.19787v1 | 2025-10-22 | Exploring the Meta Flip Graph for Matrix Multiplication | Manuel Kauers, Isaac Wood | new09 |
| 2510.18119v1 | 2025-10-20 | Constraints on the Correlation of IceCube Neutrinos with Tracers of Large-Scale Structure | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2510.16153v2 | 2025-10-17 | Cutting 4 by $n$ grids into two congruent pieces | Robert Dougherty-Bliss, Natalya Ter-Saakov, Doron Zeilberger | new11c new12 |
| 2510.14956v1 | 2025-10-16 | On Weighted and Bounded Multidimensional Catalan Numbers | Ryota Inagaki, Dimana Pramatarova | t13a |
| 2510.13403v2 | 2025-10-15 | Evidence for Neutrino Emission from X-Ray-bright Active Galactic Nuclei with IceCube | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2510.12723v1 | 2025-10-14 | Transition Matrices between Plethystic Bases of Polysymmetric Functions via Bijective Methods | Aditya Khanna | new08 |
| 2510.08156v2 | 2025-10-09 | Characterizing Liouvillian Exceptional Points Through Newton Polygons and Tropical Geometry | Sayooj P, Awadhesh Narayan | t39a |
| 2510.06142v2 | 2025-10-07 | On the generating series of the degree sequence | Quang-Khai Nguyen | new06 |
| 2510.03940v1 | 2025-10-04 | Every Fifth Real Number is Evil | Doron Zeilberger | new12 |
| 2510.01436v1 | 2025-10-01 | Symmetric Division of Linear Ordinary Differential Operators | Lixin Du, Manuel Kauers | new09 |
| 2510.00209v1 | 2025-09-30 | Limiting the Parameter Space for Unstable eV-scale Neutrinos Using IceCube Data | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2509.26138v3 | 2025-09-30 | Conjectures About Cyclic Numbers: Resolutions and Counterexamples | Duc Hieu Le | new02 |
| 2509.12726v1 | 2025-09-16 | Stoimenow matchings avoiding multiple Catalan patterns simultaneously | Shuzhen Lv, Sergey Kitaev | new08 |
| 2509.11395v1 | 2025-09-14 | Card Dealing Math | Eric Huang, Tanya Khovanova, Timur Kilybayev, Ryan Li 等 | new08 |
| 2509.08904v2 | 2025-09-10 | Hurwitz space components; and the Coleman-Oort Conjecture | Michael D. Fried | x06_fried |
| 2509.07695v2 | 2025-09-09 | Beyond No Tension: JWST z > 10 Galaxies Push Simulations to the Limit | Joe McCaffrey, Samantha Hardin, John H. Wise, John A. Regan | new01 |
| 2509.05845v1 | 2025-09-06 | Golden Ratio Growth and Phase Transitions in Chromatic Counts of Circular Chord Graphs | Rogelio N. Lopez-Bonilla, Julian Allagan, Shawn M. Langley, Angel J. Clinton | new08 |
| 2508.14711v2 | 2025-08-20 | Identification and Denoising of Radio Signals from Cosmic-Ray Air Showers using Convolutional Neural Networks | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2508.10245v1 | 2025-08-14 | The Challenge of Computing Geode Numbers | Tewodros Amdeberhan, Manuel Kauers, Doron Zeilberger | new08 new09 new12 |
| 2508.11043v1 | 2025-08-14 | Dyadically resolving trinomials for fast modular arithmetic | Robert Dougherty-Bliss, Mits Kobayashi, Natalya Ter-Saakov, Eugene Zima | new11c |
| 2508.03822v1 | 2025-08-05 | The LED calibration systems for the mDOM and D-Egg sensor modules of the IceCube Upgrade | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2507.22234v2 | 2025-07-29 | Improved measurements of the TeV-PeV extragalactic neutrino spectrum from joint analyses of IceCube tracks and cascades | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2507.22233v3 | 2025-07-29 | Evidence for a Spectral Break or Curvature in the Spectrum of Astrophysical Neutrinos from 5 TeV--10 PeV | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2507.21643v1 | 2025-07-29 | Partial Deranged Bell Numbers and Their Combinatorial Properties | Yahia Djemmada, Levent Kargın, Mümün Can | t26a |
| 2508.02690v2 | 2025-07-23 | An effective analytic recurrence for prime numbers | Benoit Cloitre | new02 |
| 2507.17947v1 | 2025-07-23 | On ascent sequences avoiding 021 and a pattern of length four | Toufik Mansour, Mark Shattuck | new08 |
| 2507.16956v4 | 2025-07-22 | On Cloitre's hiccup sequences | Robbert Fokkink, Gandhar Joshi | new08 |
| 2507.10965v2 | 2025-07-15 | Convolutive sequences, I: Through the lens of integer partition functions | Shane Chern, Dennis Eichhorn, Shishuo Fu, James A. Sellers | new08 |
| 2507.08667v2 | 2025-07-11 | The IceCube-Gen2 Collaboration -- Contributions to the 39th International Cosmic Ray Conference (ICRC2025) | R. Abbasi, M. Ackermann, J. Adams, S. K. Agarwalla 等 | new01 |
| 2507.04007v2 | 2025-07-05 | Independent Set Enumeration and Estimation of Related Constants of Grid Graphs and Their Variants | Kai Liang | new08 |
| 2507.03841v3 | 2025-07-05 | Automated Counting of Spanning Trees for Several Infinite Families of Graphs | Pablo Blanco, Doron Zeilberger | new12 |
| 2506.17862v1 | 2025-06-22 | Proofs Of Three Geode Conjectures | Tewodros Amdeberhan, Doron Zeilberger | new12 |
| 2506.12612v2 | 2025-06-14 | Non-orientable Nurikabe | Joseph Breen, Emma Copeland | new08 |
| 2506.00093v1 | 2025-05-30 | On a Family of Nested Recurrences and Their Arithmetical Solutions | Benoit Cloitre | new08 |
| 2505.20616v1 | 2025-05-27 | A stochastic Stirling engine powered by an active particle | Erick Efrain Cote-Valencia, Juan Ruben Gomez-Solano | new05 |
| 2505.14196v1 | 2025-05-20 | Even-up words and their variants | Sela Fried | new08 x05_fried x06_fried |
| 2505.13968v1 | 2025-05-20 | Two families of C1-Pk Fraeijs de Veubeke-Sander finite elements on quadrilateral meshes | Shangyou Zhang | t41a |
| 2505.12776v2 | 2025-05-19 | Independent Set Enumeration in King Graphs by Tensor Network Contractions | Kai Liang | new08 |
| 2505.10480v2 | 2025-05-15 | Some algebraic properties of ASM varieties | Ilani Axelrod-Freed, Hanson Hao, Matthew Kendall, Patricia Klein 等 | x01 |
| 2505.09275v2 | 2025-05-14 | A Littlewood-type identity for Robbins polynomials | Ilse Fischer, Hans Höngesberg | t41a |
| 2505.07304v1 | 2025-05-12 | Bounds for D-Algebraic Closure Properties | Manuel Kauers, Raphael Pages | new09 |
| 2505.05896v1 | 2025-05-09 | Consequences of the Moosbauer-Poole Algorithms | Manuel Kauers, Isaac Wood | new09 |
| 2505.05345v1 | 2025-05-08 | Creative Telescoping | Shaoshi Chen, Manuel Kauers, Christoph Koutschan | new09 new10 |
| 2505.09636v1 | 2025-05-04 | Three combinatorial sums involving central binomial coefficients | Kunle Adegoke, Robert Frontczak | t26a |
| 2504.21722v1 | 2025-04-30 | Discrete Generating Series and Linear Difference Equations | Vitaly Alekseev, Tom Cuchta, Alexander Lyapin | new06 |
| 2504.19269v1 | 2025-04-27 | Enumeration of Corona for Lozenge Tilings | Craig Knecht, Feihu Liu, Guoce Xin | new02 new08 |
| 2504.16965v1 | 2025-04-23 | Uniform treatments of Bernoulli numbers, Stirling numbers, and their generating functions | Feng Qi | t41a |
| 2504.03013v1 | 2025-04-03 | Counting k-ary words by number of adjacency differences of a prescribed size | Sela Fried, Toufik Mansour, Mark Shattuck | new08 x05_fried |
| 2504.00116v1 | 2025-03-31 | Elementary Proof of the Completeness of OEIS A051221 Below 2000 | Seiichi Azuma | new02 |
| 2503.23473v1 | 2025-03-30 | Heterogeneous Stirling numbers and heterogeneous Bell polynomials | Taekyun Kim, Dae San Kim | t24a |
| 2503.18974v3 | 2025-03-22 | An Efficient Frequency-Based Approach for Maximal Square Detection in Binary Matrices | Swastik Bhandari | new03 |
| 2503.17698v4 | 2025-03-22 | Solving tiling enumeration problems by tensor network contractions | Kai Liang | new08 |
| 2503.12277v4 | 2025-03-15 | On a conjecture of Erdős and Graham about the Sylvester's sequence | Zheng Li, Quanyu Tang | new02 |
| 2503.11734v2 | 2025-03-14 | On the records and zeros of a deterministic random walk | Henk Bruin, Robbert Fokkink | new02 |
| 2503.11055v1 | 2025-03-14 | A new combinatorial interpretation of partial sums of $m$-step Fibonacci numbers | Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini 等 | new08 |
| 2503.04122v1 | 2025-03-06 | Using Walnut to solve problems from the OEIS | Wieb Bosma, Rene Bruin, Robbert Fokkink, Jonathan Grube 等 | new08 |
| 2503.04247v2 | 2025-03-06 | On posets and polytopes attached to arbors | Frédéric Chapoton | x02 |
| 2503.03193v1 | 2025-03-05 | Saturation of 0-1 Matrices | Andrew Brahms, Alan Duan, Jesse Geneson, Jacob Greene | x04 |
| 2503.01389v1 | 2025-03-03 | Learning Conjecturing from Scratch | Thibault Gauthier, Josef Urban | new02 |
| 2503.01578v2 | 2025-03-03 | Scalar products and norm of Bethe vectors in $\mathfrak{o}_{2n+1}$ invariant integrable models | A. Liashyk, S. Pakuliak, E. Ragoucy | t26b |
| 2502.18663v3 | 2025-02-25 | CayleyPy RL: Pathfinding and Reinforcement Learning on Cayley Graphs | A. Chervov, M. Obozov, A. Soibelman, S. Lytkin 等 | new02 new08 |
| 2502.14346v1 | 2025-02-20 | Représentations des quaternions de norme 1 | Guy Henniart, Marie-France Vignéras | t26b |
| 2502.12615v5 | 2025-02-18 | Generalized Hofstadter functions $G, H$ and beyond: numeration systems and discrepancy | Pierre Letouzey | new02 new08 |
| 2502.11787v2 | 2025-02-17 | A Shape Lemma for Ideals of Differential Operators | Manuel Kauers, Christoph Koutschan, Thibaut Verron | new09 new10 |
| 2502.10212v1 | 2025-02-14 | Effective MC-finiteness | Yuval Filmus, Eldar Fischer, Johann A. Makowsky | new08 |
| 2502.08096v1 | 2025-02-12 | Hitting k primes by dice rolls | Noga Alon, Yaakov Malinovsky, Lucy Martinez, Doron Zeilberger | new12 |
| 2502.06264v1 | 2025-02-10 | Flip Graphs for Polynomial Multiplication | Shaoshi Chen, Manuel Kauers | new09 |
| 2502.03757v3 | 2025-02-06 | Non-minimality of minimal telescopers explained by residues | Shaoshi Chen, Manuel Kauers, Christoph Koutschan, Xiuyun Li 等 | new09 new10 |
| 2501.18480v3 | 2025-01-30 | The Representations of Automorphism Groups of $\mathfrak{o}$-modules of type $(\ell,1^n)$ | Alexander Jackson | x02 |
| 2501.18061v2 | 2025-01-29 | Experimenting with the Garsia-Milne Involution Principle | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2501.10849v1 | 2025-01-18 | Ordered InAs quantum dots on pre-patterned GaAs (0 0 1) by local oxidation nanolithography | J. Martín-Sánchez, Y. González, L. González, M. Tello 等 | x01 |
| 2501.05064v1 | 2025-01-09 | Equivalence of labeled graphs and lattices | Ashok Nivrutti Bhavale | new08 |
| 2501.04189v1 | 2025-01-07 | Efficient Weighted Counting of Multiset Derangements | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2501.01152v2 | 2025-01-02 | Lattice paths enumerations weighted by ascent lengths | Jun Yan | new08 |
| 2412.19730v3 | 2024-12-27 | High-dimensional permutons: theory and applications | Jacopo Borga, Andrew Lin | x01 |
| 2412.18744v1 | 2024-12-25 | Ehrhart Polynomials of Order Polytopes: Interpreting Combinatorial Sequences on the OEIS | Feihu Liu, Guoce Xin, Chen Zhang | new02 new08 |
| 2412.16517v1 | 2024-12-21 | On non-holonomicity, transcendence and $p$-adic valuations | Cristian Cobeli, Mihai Prunescu, Alexandru Zaharescu | new06 |
| 2412.11222v2 | 2024-12-15 | A Short Proof that the number of $(a,b)$-parking functions of length n $a(a+bn)^{n-1}$ | AJ Bu, Doron Zeilberger | new12 |
| 2412.08797v2 | 2024-12-11 | Maximum power Stirling-like heat engine with a harmonically confined Brownian particle | Irene Prieto-Rodríguez, Antonio Prados, Carlos A. Plata | new05 |
| 2411.19291v1 | 2024-11-28 | The Quaternary Gray Code and How It Can Be Used to Solve Ziggurat and Other Ziggu Puzzles | Madeleine Goertz, Aaron Williams | new08 |
| 2411.07662v2 | 2024-11-12 | Enumeration of pattern-avoiding alternating sign matrices: An asymptotic dichotomy | Mathilde Bouvel, Eric S. Egge, Rebecca N. Smith, Jessica Striker 等 | x01 |
| 2411.04372v3 | 2024-11-07 | Benchmarking Large Language Models with Integer Sequence Generation Tasks | Daniel O'Malley, Manish Bhattarai, Nishath Rajiv Ranasinghe, Erick Draayer 等 | new07 |
| 2411.02897v1 | 2024-11-05 | Patterns in Multi-dimensional Permutations | Shaoshi Chen, Hanqian Fang, Sergey Kitaev, Candice X. T. Zhang | new08 |
| 2411.02251v1 | 2024-11-04 | Parks: A Doubly Infinite Family of NP-Complete Puzzles and Generalizations of A002464 | Igor Minevich, Gabe Cunningham, Aditya Karan, Joshua V. Gyllinsky | new08 |
| 2410.19591v1 | 2024-10-25 | Beyond the Cascade: Juggling Vanilla Siteswap Patterns | Mario Gomez Andreu, Kai Ploeger, Jan Peters | t24b |
| 2410.15848v2 | 2024-10-21 | Symmetries of Dependency Quantified Boolean Formulas | Clemens Hofstadler, Manuel Kauers, Martina Seidl | new09 |
| 2410.16334v1 | 2024-10-19 | The $O(1/n^{85})$ Asymptotic expansion of OEIS sequence A85 | Shalosh B. Ekhad, Manuel Kauers, Doron Zeilberger | new08 new09 new12 |
| 2410.07435v2 | 2024-10-09 | The (Symbolic and Numeric) Computational Challenges of Counting 0-1 Balanced Matrices | Robert Dougherty-Bliss, Christoph Koutschan, Natalya Ter-Saakov, Doron Zeilberger | new03 new10 new11c new12 |
| 2410.06177v2 | 2024-10-08 | A finite totally nonnegative Grassmannian | John Machacek | new08 |
| 2410.07237v3 | 2024-10-06 | Proofs of some Conjectures from the OEIS | Sela Fried | x06_fried |
| 2409.18231v2 | 2024-09-26 | ReloPush: Multi-object Rearrangement in Confined Spaces with a Nonholonomic Mobile Robot Pusher | Jeeho Ahn, Christoforos Mavrogiannis | new06 |
| 2409.13395v2 | 2024-09-20 | A virtually nilpotent group whose Green series is not D-finite | Corentin Bodart | new06 |
| 2409.12129v1 | 2024-09-18 | Bayesian estimation of the number of significant principal components for cultural data | Joshua C. Macdonald, Javier Blanco-Portillo, Marcus W. Feldman, Yoav Ram | x04 |
| 2409.01442v1 | 2024-09-02 | Off-diagonal Ramsey numbers for slowly growing hypergraphs | Sam Mattheus, Dhruv Mubayi, Jiaxi Nie, Jacques Verstraëte | t41a |
| 2408.16318v2 | 2024-08-29 | Quaternary Legendre pairs II | Ilias S. Kotsireas, Christoph Koutschan, Arne Winterhof | new10 |
| 2408.12169v2 | 2024-08-22 | ReorderBench: A Benchmark for Matrix Reordering | Jiangning Zhu, Zheng Wang, Zhiyang Shen, Lai Wei 等 | new03 |
| 2408.10282v2 | 2024-08-18 | A combinatorial proof of Cramer's Rule | Doron Zeilberger | new12 |
| 2408.05311v4 | 2024-08-09 | Key-avoidance for alternating sign matrices | Mathilde Bouvel, Rebecca Smith, Jessica Striker | x01 |
| 2408.03434v2 | 2024-08-06 | The Comma Sequence is Finite in Other Bases | Robert Dougherty-Bliss, Natalya Ter-Saakov | new11c |
| 2408.02782v2 | 2024-08-05 | Log-concavity and log-convexity via distributive lattices | Jinting Liang, Bruce E. Sagan | x01 |
| 2408.01887v1 | 2024-08-04 | The Logic of Political Survival Revisited: Consequences of Elite Uncertainty Under Authoritarian Rule | Tamar Zeilberger | new12 |
| 2407.21563v1 | 2024-07-31 | A certain sequence on pure $κ-$sparse gapsets | Gilberto Brito, Stéfani Vieira | new08 |
| 2407.16155v1 | 2024-07-23 | von Neumann and Newman Pokers with Finite Decks | Tipaluck Krityakierne, Thotsaporn Aek Thanatipanonda, Doron Zeilberger | new12 |
| 2407.12218v2 | 2024-07-16 | Exploring Werner Krandick's Binary Tree Jump Statistics | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2407.02179v2 | 2024-07-02 | Graceful coloring is computationally hard | Cyriac Antony, Laavanya D., Devi Yamini S | new08 |
| 2406.18088v2 | 2024-06-26 | LLM-Driven Multimodal Opinion Expression Identification | Bonian Jia, Huiyao Chen, Yueheng Sun, Meishan Zhang 等 | new07 |
| 2406.15980v1 | 2024-06-23 | In How Ways Can You Play Stanley Solitaire? | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2406.14533v2 | 2024-06-20 | Local symmetries in partially ordered sets | Christoph Minz | new08 |
| 2406.02421v2 | 2024-06-04 | Representing Piecewise-Linear Functions by Functions with Minimal Arity | Christoph Koutschan, Anton Ponomarchuk, Josef Schicho | new10 |
| 2405.19223v1 | 2024-05-29 | On the Problem of Separating Variables in Multivariate Polynomial Ideals | Manfred Buchacher, Manuel Kauers | new09 |
| 2405.16143v2 | 2024-05-25 | Partitioning the set of natural numbers into Mersenne trees and into arithmetic progressions; Natural Matrix and Linnik's constant | Gennady Eremin | new08 |
| 2405.13561v1 | 2024-05-22 | How to Answer Questions of the Type: If you toss a coin n times, how likely is HH to show up more than HT? | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2405.08133v1 | 2024-05-13 | Asymptotics of bivariate algebraico-logarithmic generating functions | Torin Greenwood, Tristan Larson | new06 |
| 2405.03322v1 | 2024-05-06 | Enhancing Aeroacoustic Wind Tunnel Studies through Massive Channel Upscaling with MEMS Microphones | Daniel Ernst, Armin Goudarzi, Reinhard Geisler, Florian Philipp 等 | x01 |
| 2405.03079v1 | 2024-05-05 | Explicit Expressions for the First 20 Moments of the Area Under Dyck and Motzkin Paths | AJ Bu, Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2405.02430v2 | 2024-05-03 | How to generate all possible rational Wilf-Zeilberger forms? | Shaoshi Chen, Christoph Koutschan, Yisen Wang | new10 |
| 2405.00881v1 | 2024-05-01 | Bijective and Automated Approaches to Abel Sums | Gil Kalai, Doron Zeilberger | new12 |
| 2404.17694v3 | 2024-04-26 | Areas Between Cosines | Muhammad Adam Dombrowski, Gregory Dresden | new08 |
| 2404.16404v1 | 2024-04-25 | Counting $U(N)^{\otimes r}\otimes O(N)^{\otimes q}$ invariants and tensor model observables | Remi Cocou Avohou, Joseph Ben Geloun, Reiko Toriumi | x01 |
| 2404.10221v2 | 2024-04-16 | On $τ$-preconditioners for a quasi-compact difference scheme to Riesz fractional diffusion equations with variable coefficients | Zi-Hang She, Xue Zhang, Xian-Ming Gu, Stefano Serra-Capizzano | t26b |
| 2404.08193v2 | 2024-04-12 | Integers that are not the sum of positive powers | Brennan Benfield, Oliver Lippard | new02 |
| 2404.08190v1 | 2024-04-12 | End behavior of Ramanujan's taxicab numbers | Brennan Benfield, Oliver Lippard, Arindam Roy | new02 new08 |
| 2404.05276v1 | 2024-04-08 | On the complexity of normalization for the planar $λ$-calculus | Anupam Das, Damiano Mazza, Lê Thành Dũng Nguyên, Noam Zeilberger | new12 |
| 2404.01483v3 | 2024-04-01 | Creating Decidable Diophantine Equations | Robert Dougherty-Bliss, Charles Kenney, Doron Zeilberger | new11c new12 |
| 2403.08120v5 | 2024-03-12 | Progressive and Rushed Dyck Paths | Axel Bacher | new08 |
| 2403.07009v1 | 2024-03-09 | Solving Functional Equations Dear to W.T. Tutte using the Naive (yet fullly rigorous!) Guess And Check Method | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2403.04413v1 | 2024-03-07 | Sharp estimates for convolution operators associated to hypersurfaces in $\mathbb{R}^3$ with height $h\le2$ | Ibrokhimbek Akramov, Isroil A. Ikromov | t39a |
| 2402.15063v2 | 2024-02-23 | Efficient Evaluations of Weighted Sums over the Boolean Lattice inspired by conjectures of Berti, Corsi, Maspero, and Ventura | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2402.13051v1 | 2024-02-20 | Symmetric Power L-functions of the hyper-Kloosterman Family | C. Douglas Haessig, Steven Sperber | t39a |
| 2402.11979v2 | 2024-02-19 | On a q-analogue of the Zeta polynomial of posets | Frédéric Chapoton | x02 |
| 2402.09827v2 | 2024-02-15 | A counterexample to the Pellian equation conjecture of Mordell | Andreas Reinhart | new02 |
| 2402.05938v1 | 2024-02-08 | The Jackson-Richmond 4CT Constant is EXACTLY 10/27 | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2402.04684v2 | 2024-02-07 | Parallel Summation in P-Recursive Extensions | Shaoshi Chen, Ruyong Feng, Manuel Kauers, Xiuyun Li | new09 |
| 2401.16334v2 | 2024-01-29 | Right-angled triangles with almost prime hypotenuse | Cihan Sabuncu | new02 |
| 2401.14627v1 | 2024-01-26 | Simple Generating Functions for Certain Young Tableaux with Periodic Walls | Feihu Liu, Guoce Xin | new08 |
| 2401.12430v1 | 2024-01-23 | Enumerating Seating Arrangements that Obey Social Distancing | George Spahn, Doron Zeilberger | new12 |
| 2401.08481v1 | 2024-01-16 | Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations | Christoph Koutschan, Christian Krattenthaler, Michael Schlosser | new10 |
| 2405.14703v4 | 2023-12-29 | The categorical contours of the Chomsky-Schützenberger representation theorem | Paul-André Melliès, Noam Zeilberger | new12 |
| 2312.13098v4 | 2023-12-20 | A simple proof for generalized Fibonacci numbers with dying rabbits | Roberto De Prisco | new06 |
| 2312.11446v1 | 2023-12-18 | An intermediate case of exponential multivalued forbidden matrix configuration | Wallace Peaslee, Attila Sali, Jun Yan | x04 |
| 2312.04144v1 | 2023-12-07 | A sum up method for solving summations of the form $\sum_{k=n_0}^{n} A_{n,k}$ and rising and falling factorial transforms | Parham Zarghami | t24a |
| 2311.15576v1 | 2023-11-27 | Quadrature Rules on Triangles and Tetrahedra for Multidimensional Summation-By-Parts Operators | Zelalem Arega Worku, Jason E. Hicken, David W. Zingg | t41a |
| 2311.08342v2 | 2023-11-14 | Sparse Linear Regression with Constraints: A Flexible Entropy-based Framework | Amber Srivastava, Alisina Bayati, Srinivasa Salapaka | new03 |
| 2311.05246v1 | 2023-11-09 | Reduction-based Creative Telescoping for P-recursive Sequences via Integral Bases | Shaoshi Chen, Lixin Du, Manuel Kauers, Rong-Hua Wang | new09 |
| 2311.03011v2 | 2023-11-06 | Full Grid Lattice Polygons with Maximal Sum of Squares of Edge-Lengths | Oliver Mantas Ališauskas, Giedrius Alkauskas, Valdas Dičiūnas | new02 new08 |
| 2310.18153v1 | 2023-10-27 | Implementing and Experimenting with the Calabi-Wilf algorithm for random selection of a subspace over a finite field | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2310.02987v2 | 2023-10-04 | Variance Reduced Halpern Iteration for Finite-Sum Monotone Inclusions | Xufeng Cai, Ahmet Alacaoglu, Jelena Diakonikolas | t26b |
| 2309.11589v2 | 2023-09-20 | Output-Feedback Nonlinear Model Predictive Control with Iterative State- and Control-Dependent Coefficients | Mohammadreza Kamaldar, Dennis S. Bernstein | new06 |
| 2309.08446v3 | 2023-09-15 | Diagonally symmetric alternating sign matrices | Roger E. Behrend, Ilse Fischer, Christoph Koutschan | new10 |
| 2309.08762v1 | 2023-09-15 | Explicit Expressions for Moments of the Duration of a 3-Player Gambler's Ruin | Shalosh B. Ekhad, Doron Zeilberger | new12 |
| 2309.06518v4 | 2023-09-12 | Pattern Avoidance in Weak Ascent Sequences | Beáta Bényi, Toufik Mansour, José L. Ramírez | new03 x01 |
| 2309.02925v1 | 2023-09-06 | Collisionless shock region of the KdV equation and an entry in Gradshteyn and Ryzhik | Tewodros Amdeberhan, Victor Moll, John Lopez Santander, Ken McLaughlin 等 | new10 |
| 2309.00487v1 | 2023-09-01 | Hardinian Arrays | Robert Dougherty-Bliss, Manuel Kauers | new02 new08 new09 new11c |
| 2308.12094v1 | 2023-08-23 | On the Ternary Purely Exponential Diophantine Equation $(ak)^x+(bk)^y=((a+b)k)^z$ with Prime Powers $a$ and $b$ | Maohua Le, Gökhan Soydan | new02 |
| 2308.10332v4 | 2023-08-20 | Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers | Robert S. Maier | new04 x03 t38a t26a |
| 2308.09344v2 | 2023-08-18 | On a conjecture on pattern-avoiding machines | Christopher Bao, Giulio Cerbai, Yunseo Choi, Katelyn Gan 等 | new02 new08 |
| 2307.16069v4 | 2023-07-29 | Lots and Lots of Perrin-Type Primality Tests and Their Pseudo-Primes | Robert Dougherty-Bliss, Doron Zeilberger | new11c |
| 2307.01912v3 | 2023-07-04 | Yay for Determinants! | Tewodros Amdeberhan, Christoph Koutschan, Doron Zeilberger | new10 |
| 2306.10318v1 | 2023-06-17 | Dyck Numbers, IV. Nested patterns in OEIS A036991 | Gennady Eremin | new08 |
| 2306.00882v1 | 2023-06-01 | Some New Non-Commutative Matrix Multiplication Algorithms of Size $(n,m,6)$ | Manuel Kauers, Jakob Moosbauer | new09 |
| 2305.16933v1 | 2023-05-26 | Representing Piecewise Linear Functions by Functions with Small Arity | Christoph Koutschan, Bernhard Moser, Anton Ponomarchuk, Josef Schicho | new10 |
| 2304.02986v1 | 2023-04-06 | A Mathematical Benchmark for Inductive Theorem Provers | Thibault Gauthier, Chad E. Brown, Mikolas Janota, Josef Urban | new02 |
| 2304.02200v6 | 2023-04-05 | Zeta-polynomials, superpolynomials, DAHA and plane curve singularities | Ivan Cherednik | x02 |
| 2304.02471v7 | 2023-04-03 | On the Number of Regular Integers Modulo $n$ and Its Significance for Cryptography | Klaus Dohmen, Mandy Lange-Geisler | new08 |
| 2304.00716v2 | 2023-04-03 | A spectral extremal problem on non-bipartite triangle-free graphs | Yongtao Li, Lihua Feng, Yuejian Peng | t13a |
| 2303.18175v1 | 2023-03-31 | About a combinatorial problem with $n$ seats and $n$ people | Simon Wundling | new08 |
| 2303.10223v1 | 2023-03-17 | Hessenberg-Toeplitz Matrix Determinants with Schroder and Fine Number Entries | Taras Goy, Mark Shattuck | new08 |
| 2303.02793v2 | 2023-03-05 | Some D-finite and Some Possibly D-finite Sequences in the OEIS | Manuel Kauers, Christoph Koutschan | new02 new06 new08 new09 new10 |
| 2303.02560v4 | 2023-03-05 | On Potentials Integrated by the Nikiforov-Uvarov Method | Lina Ellis, Ikumi Ellis, Christoph Koutschan, Sergei K. Suslov | new10 |
| 2302.06396v2 | 2023-02-13 | Transcendence Certificates for D-finite Functions | Manuel Kauers, Christoph Koutschan, Thibaut Verron | new09 new10 |
| 2302.06244v1 | 2023-02-13 | Fast evaluation and root finding for polynomials with floating-point coefficients | Rémi Imbach, Guillaume Moroz | t39a |
| 2302.04606v1 | 2023-02-09 | On Discovering Interesting Combinatorial Integer Sequences | Martin Svatoš, Peter Jung, Jan Tóth, Yuyi Wang 等 | new08 |
| 2302.04652v1 | 2023-02-09 | Hermite Reduction for D-finite Functions via Integral Bases | Shaoshi Chen, Lixin Du, Manuel Kauers | new09 |
| 2302.04070v1 | 2023-02-08 | Order bounds for $C^2$-finite sequences | Manuel Kauers, Philipp Nuspl, Veronika Pillwein | new09 |
| 2302.04067v2 | 2023-02-08 | A Unified Approach to Unimodality of Gaussian Polynomials | Christoph Koutschan, Ali K. Uncu, Elaine Wong | new10 |
| 2302.02765v1 | 2023-02-06 | Dyck Numbers, III. Enumeration and bijection with symmetric Dyck paths | Gennady Eremin | new08 |
| 2301.03475v2 | 2023-01-09 | Integrality relations for polygonal dissections | Aaron Abrams, Jamie Pommersheim | t41a |
| 2301.00644v1 | 2022-12-28 | Equivalent conditions for the $n$th element of the Beatty sequence $B_{\sqrt{2}}$ being even | Sela Fried | x05_fried x06_fried |
| 2212.01175v1 | 2022-12-02 | Flip Graphs for Matrix Multiplication | Manuel Kauers, Jakob Moosbauer | new09 |
| 2211.14482v2 | 2022-11-26 | The gerrymander sequence, or A348456 | Anthony J Guttmann, Iwan Jensen | new02 |
| 2211.12397v4 | 2022-11-22 | Uncountably many enumerations of well-quasi-ordered permutation classes | Robert Brignall, Vincent Vatter | new06 |
| 2211.08175v2 | 2022-11-15 | The Orbit-Sum Method for Higher Order Equations | Manfred Buchacher, Manuel Kauers | new09 |
| 2211.04709v1 | 2022-11-09 | Carnot, Stirling, Ericsson stochastic heat engines: Efficiency at maximum power | O. Contreras-Vergara, N. Sánchez-Salas, G. Valencia-Ortega, J. I. Jiménez-Aquino | new05 |
| 2211.04112v1 | 2022-11-08 | Improved Pattern-Avoidance Bounds for Greedy BSTs via Matrix Decomposition | Parinya Chalermsook, Manoj Gupta, Wanchote Jiamjitrak, Nidia Obscura Acosta 等 | x01 |
| 2211.01135v1 | 2022-11-02 | Dyck Numbers, II. Triplets and Rooted Trees in OEIS A036991 | Gennady Eremin | new02 |
| 2210.13520v1 | 2022-10-24 | Gosper's algorithm and Bell numbers | Robert Dougherty-Bliss | new11c |
| 2210.04045v3 | 2022-10-08 | The FBHHRBNRSSSHK-Algorithm for Multiplication in $\mathbb{Z}_2^{5\times5}$ is still not the end of the story | Manuel Kauers, Jakob Moosbauer | new09 |
| 2209.13134v2 | 2022-09-27 | An $O(3.82^k)$ Time FPT Algorithm for Convex Flip Distance | Haohong Li, Ge Xia | t41a |
| 2209.12436v2 | 2022-09-26 | Statistics on clusters and $r$-Stirling permutations | Sergi Elizalde, Justin M. Troyka, Yan Zhuang | t24a |
| 2209.12256v1 | 2022-09-25 | On the Cryptomorphism between Davis' Subset Lattices, Atomic Lattices, and Closure Systems under T1 Separation Axiom | Dmitry I. Ignatov | new02 |
| 2209.12137v1 | 2022-09-25 | Burstein's permutation conjecture, Hong and Li's inversion sequence conjecture, and restricted Eulerian distributions | Shane Chern, Shishuo Fu, Zhicong Lin | new02 |
| 2209.12147v2 | 2022-09-25 | Factor analysis for a mixture of continuous and binary random variables | Takashi Arai | x04 |
| 2209.10990v2 | 2022-09-22 | Polynomial Moments with a weighted Zeta Square measure on the critical line | Sébastien Darses, Erwan Hillion | t26a |
| 2209.01787v3 | 2022-09-05 | How does the Gerrymander Sequence Continue? | Manuel Kauers, Christoph Koutschan, George Spahn | new09 new10 |
| 2208.08506v5 | 2022-08-17 | On $d$-permutations and Pattern Avoidance Classes | Nathan Sun | new02 |
| 2208.06932v2 | 2022-08-14 | Partition Rank and Partition Lattices | Mohamed Omar | t41a |
| 2208.03788v4 | 2022-08-07 | On a conjecture of McNeil | Sela Fried | x06_fried |
| 2207.13886v2 | 2022-07-28 | A Brownian cyclic engine operating in a viscoelastic active suspension | Carlos Antonio Guevara-Valadez, Rahul Marathe, Juan Ruben Gomez-Solano | new05 |
| 2207.10224v2 | 2022-07-20 | Triangular Recurrences, Generalized Eulerian Numbers, and Related Number Triangles | Robert S. Maier | t26a t13a |
| 2207.08251v3 | 2022-07-17 | Maximum norm a posteriori error estimates for convection-diffusion problems | Alan Demlow, Sebastian Franz, Natalia Kopteva | t26b |
| 2206.14852v1 | 2022-06-29 | The Meta-C-finite Ansatz | Robert Dougherty-Bliss | new11c |
| 2206.08965v3 | 2022-06-17 | KitBit: A New AI Model for Solving Intelligence Tests and Numerical Series | Víctor Corsino, José Manuel Gilpérez, Luis Herrera | new07 |
| 2206.08837v1 | 2022-06-17 | Moment Generating Stirling Numbers and Applications | Ludwig Frank | t26a |
| 2206.04089v1 | 2022-06-08 | On Minimally Non-Firm Binary Matrices | Reka Agnes Kovacs | new03 |
| 2206.00550v1 | 2022-06-01 | A Normal Form for Matrix Multiplication Schemes | Manuel Kauers, Jakob Moosbauer | new09 |
| 2205.13601v1 | 2022-05-26 | Exploring General Apéry Limits via the Zudilin-Straub t-transform | Robert Dougherty-Bliss, Doron Zeilberger | new11c |
| 2205.10163v4 | 2022-05-19 | On some open problems concerning perfect powers | Marco Ripà | new02 |
| 2205.06004v3 | 2022-05-12 | Paths through equally spaced points on a circle | Brendan D. McKay, Tim Peters | new02 |
| 2205.06030v1 | 2022-05-12 | Order-Degree-Height Surfaces for Linear Operators | Hui Huang, Manuel Kauers, Gargi Mukherjee | new09 |
| 2204.12401v3 | 2022-04-26 | Jet Functors in Noncommutative Geometry | Keegan J. Flood, Mauro Mantegazza, Henrik Winther | new06 |
| 2204.09228v3 | 2022-04-20 | Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities | Yang Cai, Argyris Oikonomou, Weiqiang Zheng | t26b |
| 2204.04663v3 | 2022-04-10 | A note on "exotic integrals" | Anton A. Kutsenko | t26a |
| 2203.07573v2 | 2022-03-15 | Thermodynamic engine powered by anisotropic fluctuations | Olga Movilla Miangolarra, Amirhossein Taghvaei, Yongxin Chen, Tryphon T. Georgiou | new05 |
| 2203.03381v1 | 2022-02-25 | On a variant of the happy numbers and their generalizations | Luca Onnis | new02 |
| 2202.07966v2 | 2022-02-16 | Guessing with Little Data | Manuel Kauers, Christoph Koutschan | new09 new10 |
| 2202.07715v3 | 2022-02-15 | Combinatorial Exploration: An algorithmic framework for enumeration | Michael H. Albert, Christian Bean, Anders Claesson, Émile Nadeau 等 | x01 |
| 2201.13253v1 | 2022-01-31 | On Two Families of Generalizations of Pascal's Triangle | Michael A. Allen, Kenneth Edwards | t41a |
| 2201.12503v3 | 2022-01-29 | Polygon recutting as a cluster integrable system | Anton Izosimov | t41a |
| 2201.08490v3 | 2022-01-21 | Tridiagonal real symmetric matrices with a connection to Pascal's triangle and the Fibonacci sequence | Emily Gullerud, Rita Johnson, aBa Mbirika | t41a |
| 2201.02376v1 | 2022-01-07 | Proving some conjectures on Kekulé numbers for certain benzenoids by using Chebyshev polynomials | Guoce Xin, Yueming Zhong | new02 |
| 2201.00533v1 | 2022-01-03 | Realizations of Rigid Graphs | Christoph Koutschan | new10 |
| 2112.00479v4 | 2021-12-01 | Set partitions, tableaux, and subspace profiles under regular diagonal matrices | Amritanshu Prasad, Samrith Ram | t41a |
| 2111.11527v2 | 2021-11-22 | Permutations with non-decreasing transposition array and pattern avoidance | Fufa Beyene, Roberto Mantaci | x01 |
| 2111.08796v1 | 2021-11-16 | Apéry limits for elliptic $L$-values | Christoph Koutschan, Wadim Zudilin | new10 |
| 2111.03159v2 | 2021-11-04 | Weak ascent sequences and related combinatorial structures | Beáta Bényi, Anders Claesson, Mark Dukes | new03 x01 |
| 2111.02105v3 | 2021-11-03 | Legendre pairs of lengths $\ell\equiv0$ (mod 5) | Ilias Kotsireas, Christoph Koutschan, Dursun Bulutoglu, David Arquette 等 | new10 |
| 2109.09928v3 | 2021-09-21 | A numerical study of L-convex polyominoes and 201-avoiding ascent sequences | Anthony Guttmann, Vaclav Kotesovec | new06 |
| 2109.09574v3 | 2021-09-20 | On the representation of non-holonomic univariate power series | Bertrand Teguia Tabuguia, Wolfram Koepf | new06 |
| 2109.10238v4 | 2021-09-16 | Distribution of Square Prime Numbers | Raghavendra N. Bhat | new02 |
| 2109.08177v2 | 2021-09-16 | Profile decomposition in Sobolev spaces and decomposition of integral functionals II: homogeneous case | Mizuho Okumura | t26b |
| 2109.08176v3 | 2021-09-16 | Profile decomposition in Sobolev spaces and decomposition of integral functionals I: inhomogeneous case | Mizuho Okumura | t26b |
| 2109.05359v2 | 2021-09-11 | Experimenting with Apery Limits and WZ pairs | Robert Dougherty-Bliss, Doron Zeilberger | new11c |
| 2109.02112v1 | 2021-09-05 | P-finite Recurrences From Generating Functions with Roots of Polynomials | Richard J. Mathar | new06 |
| 2109.00605v2 | 2021-09-01 | Backstepping Mean-Field Density Control for Large-Scale Heterogeneous Nonlinear Stochastic Systems | Tongjia Zheng, Qing Han, Hai Lin | new06 |
| 2108.03590v1 | 2021-08-08 | On the positive zeros of generalized Narayana polynomials related to the Boros-Moll polynomials | James J. Y. Zhao | t13a |
| 2106.13434v2 | 2021-06-25 | Binary Matrix Factorisation and Completion via Integer Programming | Reka A. Kovacs, Oktay Gunluk, Raphael A. Hauser | new03 |
| 2105.09826v1 | 2021-05-20 | Incidence Monoids: Automorphisms and Complexity | Mahir Bilen Can | x02 |
| 2105.08539v2 | 2021-05-18 | Binomial Determinants for Tiling Problems Yield to the Holonomic Ansatz | Hao Du, Christoph Koutschan, Thotsaporn Thanatipanonda, Elaine Wong | new10 |
| 2105.02452v1 | 2021-05-06 | Annihilation and recurrence of vortex-antivortex pairs in two-component Bose-Einstein condensates | Junsik Han, Makoto Tsubota | t39b |
| 2104.14516v1 | 2021-04-29 | Constructions in combinatorics via neural networks | Adam Zsolt Wagner | x01 |
| 2104.04637v4 | 2021-04-09 | New Quantum-Safe Versions of Decisional Diffie-Hellman Assumption in the General Linear Group and Their Applications: Two New Key-agreements | Abdelhaliem Babiker | new03 |
| 2103.16720v3 | 2021-03-30 | How to hunt wild constants | David R. Stoutemyer | new02 |
| 2103.15291v2 | 2021-03-29 | Recurrence relations of poly-Cauchy numbers by the $r$-Stirling transform | Takao Komatsu | new04 x03 |
| 2103.11960v1 | 2021-03-17 | New series with Cauchy and Stirling numbers, Part 2 | Khristo N. Boyadzhiev, Levent Kargın | t26a |
| 2102.10170v1 | 2021-02-19 | Integral Recurrences from A to Z | Robert Dougherty-Bliss | new11c |
| 2102.06538v2 | 2021-02-12 | Lazy Hermite Reduction and Creative Telescoping for Algebraic Functions | Shaoshi Chen, Lixin Du, Manuel Kauers | new09 |
| 2101.10686v8 | 2021-01-26 | Maclaurin's series expansions for positive integer powers of inverse (hyperbolic) sine and related functions, specific values of partial Bell polynomials, and two applications | Bai-Ni Guo, Dongkyu Lim, Feng Qi | t26a |
| 2101.10147v1 | 2021-01-25 | There are EXACTLY 1493804444499093354916284290188948031229880469556 Ways to Derange a Standard Deck of Cards (ignoring suits) [and many other such useful facts] | Shalosh B. Ekhad, Christoph Koutschan, Doron Zeilberger | new10 |
| 2101.08308v1 | 2021-01-20 | Tweaking the Beukers Integrals In Search of More Miraculous Irrationality Proofs A La Apery | Robert Dougherty-Bliss, Christoph Koutschan, Doron Zeilberger | new10 new11c |
| 2101.03116v3 | 2021-01-08 | Legendre pairs of lengths $\ell \equiv 0$ (mod $3$) | Ilias Kotsireas, Christoph Koutschan | new10 |
| 2012.14991v3 | 2020-12-30 | Symmetric Fibonaccian distributive lattices and representations of the special linear Lie algebras | Robert G. Donnelly, Molly W. Dunkum, Sasha V. Malone, Alexandra Nance | new02 |
| 2012.15307v1 | 2020-12-30 | Matrix products of binomial coefficients and unsigned Stirling numbers | Marin Knežević, Vedran Krčadinac, Lucija Relić | t26a |
| 2012.00816v3 | 2020-12-01 | The generating function of Kreweras walks with interacting boundaries is not algebraic | Alin Bostan, Manuel Kauers, Thibaut Verron | new09 |
| 2011.14360v1 | 2020-11-29 | Asymptotics of descent functions | Kaarel Hänni | t41a |
| 2011.13373v1 | 2020-11-26 | Quadrant Walks Starting Outside the Quadrant | Manfred Buchacher, Manuel Kauers, Amelie Trotignon | new09 |
| 2011.08155v1 | 2020-11-16 | Sequence Positivity Through Numeric Analytic Continuation: Uniqueness of the Canham Model for Biomembranes | Stephen Melczer, Marc Mezzarobba | new06 |
| 2010.13364v2 | 2020-10-26 | Low-Rank Matrix Recovery with Scaled Subgradient Methods: Fast and Robust Convergence Without the Condition Number | Tian Tong, Cong Ma, Yuejie Chi | t26b |
| 2010.08889v2 | 2020-10-18 | Creative Telescoping on Multiple Sums | Christoph Koutschan, Elaine Wong | new10 |
| 2009.09061v1 | 2020-09-18 | Enumerating Restricted Dyck Paths with Context-Free Grammars | AJ Bu, Robert Dougherty-Bliss | new11c |
| 2009.04546v1 | 2020-09-09 | New Results on Pattern-Replacement Equivalences: Generalizing a Classical Theorem and Revising a Recent Conjecture | Michael Ma | new02 |
| 2007.15562v6 | 2020-07-30 | Down-step statistics in generalized Dyck paths | Andrei Asinowski, Benjamin Hackl, Sarah J. Selkirk | new03 |
| 2006.16180v1 | 2020-06-29 | Binary Random Projections with Controllable Sparsity Patterns | Wenye Li, Shuzhong Zhang | new03 |
| 2006.10205v2 | 2020-06-17 | Counting Standard Young Tableaux With Restricted Runs | Manuel Kauers, Doron Zeilberger | new02 new09 |
| 2006.05878v1 | 2020-06-10 | Variable dimension non-overlapping matrices | Elena Barcucci, Antonio Bernini, Renzo Pinzani | new03 |
| 2006.01623v2 | 2020-06-02 | Good pivots for small sparse matrices | Manuel Kauers, Jakob Moosbauer | new09 |
| 2005.12380v1 | 2020-05-25 | Common Factors in Fraction-Free Matrix Decompositions | Johannes Middeke, David J. Jeffrey, Christoph Koutschan | new10 |
| 2005.08491v1 | 2020-05-18 | Construction and heat kernel estimates of general stable-like Markov processes | V. Knopova, A. Kulik, R. Schilling | t26b |
| 2005.04281v1 | 2020-05-08 | Rational dynamical systems, $S$-units, and $D$-finite power series | Jason P. Bell, Shaoshi Chen, Ehsaan Hossain | new06 |
| 2005.00379v2 | 2020-05-01 | Pattern-Avoiding (0,1)-Matrices | Richard A. Brualdi, Lei Cao | x01 |
| 2004.14238v1 | 2020-04-29 | Walks with Small Steps in the 4D-Orthant | Manfred Buchacher, Sophie Hofmanninger, Manuel Kauers | new09 |
| 2004.12490v2 | 2020-04-26 | Slopes in eigenvarieties for definite unitary groups | Lynnelle Ye | t39a |
| 2004.06921v3 | 2020-04-15 | Linear $k$-Chord Diagrams | Donovan Young | t13a |
| 2004.00090v3 | 2020-03-31 | Automatic Conjecturing and Proving of Exact Values of Some Infinite Families of Infinite Continued Fractions | Robert Dougherty-Bliss, Doron Zeilberger | new11c |
| 2003.01255v1 | 2020-03-02 | Height Gap Conjectures, $D$-Finiteness, and Weak Dynamical Mordell-Lang | Jason P. Bell, Fei Hu, Matthew Satriano | new06 |
| 2002.11622v1 | 2020-02-26 | Revisiting compact RDF stores based on k2-trees | Nieves R. Brisaboa, Ana Cerdeira-Pena, Guillermo de Bernardo, Antonio Fariña | new03 |
| 2002.07342v1 | 2020-02-18 | An Upper Bound for Sorting $R_n$ with LRE | Sai Satwik Kuppili, Bhadrachalam Chitturi | new02 |
| 2002.02783v1 | 2020-02-07 | Integral P-Recursive Sequences | Shaoshi Chen, Lixin Du, Manuel Kauers, Thibaut Verron | new06 new09 |
| 2002.02845v2 | 2020-02-07 | Gevrey estimates of formal solutions for certain moment partial differential equations with variable coefficients | Maria Suwińska | t39a |
| 2002.01541v2 | 2020-02-04 | Separating Variables in Bivariate Polynomial Ideals | Manfred Buchacher, Manuel Kauers, Gleb Pogudin | new09 |
| 2002.00789v2 | 2020-02-03 | Diagonals of rational functions: from differential algebra to effective algebraic geometry (unabridged version) | Y. Abdelaziz, S. Boukraa, C. Koutschan, J-M. Maillard | new10 |
| 2001.11599v2 | 2020-01-30 | Calculation and Properties of Zonal Polynomials | Lin Jiu, Christoph Koutschan | new10 |
| 1912.06221v2 | 2019-12-12 | An affine reconstructed algorithm for diffusion on triangular grids using the nodal discontinuous Galerkin method | Yang Song, Bhuvana Srinivasan | t41a |
| 1912.03674v3 | 2019-12-08 | Inversion sequences avoiding pairs of patterns | Chunyan Yan, Zhicong Lin | new02 |
| 1912.02909v2 | 2019-12-05 | Newton Polygons of Hecke Operators | Liubomir Chiriac, Andrei Jorza | t39a |
| 1911.11998v1 | 2019-11-27 | Estimates of formal solutions for some generalized moment partial differential equations | Alberto Lastra, Sławomir Michalik, Maria Suwińska | t39a |
| 1911.10288v1 | 2019-11-23 | On sequences associated to the invariant theory of rank two simple Lie algebras | Alin Bostan, Jordan Tirrell, Bruce W. Westbury, Yi Zhang | new02 |
| 1910.13669v2 | 2019-10-30 | An Investigation Into Several Explicit Versions of Burgess' Bound | Forrest J. Francis | t26b |
| 1910.12774v2 | 2019-10-28 | Missing Not at Random in Matrix Completion: The Effectiveness of Estimating Missingness Probabilities Under a Low Nuclear Norm Assumption | Wei Ma, George H. Chen | x04 |
| 1910.08855v1 | 2019-10-19 | A Recursion for the FiboNarayana and the Generalized Narayana Numbers | Kristina Garrett, Kendra Killpatrick | t13a |
| 1910.03490v1 | 2019-10-07 | Summing Formulas For Generalized Tribonacci Numbers | Yüksel Soykan | t13a |
| 1908.01981v4 | 2019-08-06 | Monotonic Representations of Outerplanar Graphs as Edge Intersection Graphs of Paths on a Grid | Eranda Cela, Elisabeth Gaar | x04 |
| 1907.10950v2 | 2019-07-25 | Cosmology of Lorentz fiber-bundle induced scalar-tensor theories | Satoshi Ikeda, Emmanuel N. Saridakis, Panayiotis C. Stavrinos, Alkiviadis Triantafyllopoulos | new06 |
| 1907.04251v2 | 2019-07-09 | A divide-and-conquer algorithm for binary matrix completion | Melanie Beckerleg, Andrew Thompson | new03 |
| 1907.01126v2 | 2019-07-02 | Nonlinear stability of explicit self-similar solutions for the timelike extremal hypersurfaces in R^{1+3} | Weiping Yan | t39a |
| 1907.00697v1 | 2019-07-01 | The Trustworthy Pal: Controlling the False Discovery Rate in Boolean Matrix Factorization | Sibylle Hess, Nico Piatkowski, Katharina Morik | new03 |
| 1906.11970v1 | 2019-06-27 | On nested and 2-nested graphs: two subclasses of graphs between threshold and split graphs | Nina Pardal, Guillermo A. Durán, Luciano N. Grippo, Martín D. Safe | x04 |
| 1905.06450v1 | 2019-05-15 | D-finiteness, rationality, and height | Jason P. Bell, Khoa D. Nguyen, Umberto Zannier | new06 |
| 1904.05731v1 | 2019-04-11 | Zeta-polynomials, Hilbert polynomials, and the Eichler-Shimura identities | Marie Jameson | x02 |
| 1903.08946v1 | 2019-03-21 | On partially ordered patterns of length 4 and 5 in permutations | Alice L. L. Gao, Sergey Kitaev | new02 |
| 1903.03281v4 | 2019-03-08 | On Eisenstein polynomials and zeta polynomials II | Tsuyoshi Miezaki, Manabu Oura | x02 |
| 1901.04629v2 | 2019-01-15 | A Hamiltonian-Level Certificate for Network-Free Distributed Quantum Simulation:Exact Tensor-Separability Criterion and Approximate Residual Bounds | Kan He, Shusen Liu, Jinchuan Hou, Pascal Jahan Elahi 等 | t26b |
| 1811.12897v1 | 2018-11-30 | Restricted $r$-Stirling Numbers and their Combinatorial Applications | Beáta Bényi, Miguel Méndez, José L. Ramírez, Tanay Wakhare | t24a |
| 1810.11390v1 | 2018-10-26 | Joint Estimation of DOA and Frequency with Sub-Nyquist Sampling in a Binary Array Radar System | Zhan Zhang, Ping Wei, Lijuan Deng, Huaguo Zhang | new03 |
| 1810.10987v5 | 2018-10-25 | Nuclear Norm Regularized Estimation of Panel Regression Models | Hyungsik Roger Moon, Martin Weidner | t26b |
| 1810.03409v1 | 2018-10-08 | On the Domination Number of Permutation Graphs and an Application to Strong Fixed Points | Theresa Baren, Michael Cory, Mia Friedberg, Peter Gardner 等 | new02 |
| 1809.03557v2 | 2018-09-10 | Keep Rollin' - Whole-Body Motion Control and Planning for Wheeled Quadrupedal Robots | Marko Bjelonic, C. Dario Bellicoso, Yvain de Viragh, Dhionis Sako 等 | new06 |
| 1808.06782v1 | 2018-08-21 | The divisibility of zeta functions of cyclotomic function fields | Daisuke Shiomi | x02 |
| 1807.11505v2 | 2018-07-30 | Refining the bijections among ascent sequences, (2+2)-free posets, integer matrices and pattern-avoiding permutations | Mark Dukes, Peter R. W. McNamara | x01 |
| 1807.10714v5 | 2018-07-27 | Tropical recurrent sequences | Dima Grigoriev | t39a |
| 1807.06570v3 | 2018-07-17 | Representation Growth of Compact Special Linear Groups of degree two | M Hassain, Pooja Singla | x02 |
| 1807.03415v1 | 2018-07-09 | Fast Kinodynamic Bipedal Locomotion Planning with Moving Obstacles | Junhyeok Ahn, Orion Campbell, Donghyun Kim, Luis Sentis | new06 |
| 1807.02744v3 | 2018-07-08 | On Eisenstein polynomials and zeta polynomials | Tsuyoshi Miezaki | x02 |
| 1807.02411v1 | 2018-07-05 | Improved bounds on the extremal function of hypergraphs | William Zhang | x01 |
| 1807.01062v1 | 2018-07-03 | Positivity of iterated sequences of polynomials | Bao-Xuan Zhu | t13a |
| 1806.00887v1 | 2018-06-03 | On Calculating the Coefficients of a Polynomial Generated Sequence Using the Worpitzky Number Triangles | John K. Sikora | t41a |
| 1805.05991v2 | 2018-05-15 | Stabilization of Control-Affine Systems by Local Approximations of Trajectories | Raik Suttner | new06 |
| 1804.06265v3 | 2018-04-17 | Pattern Avoidance of Generalized Permutations | Zhousheng Mei, Suijie Wang | x01 |
| 1804.01597v1 | 2018-04-04 | Counting with Borel's Triangle | Yue Cai, Catherine Yan | x01 |
| 1803.09003v1 | 2018-03-23 | On the structure of matrices avoiding interval-minor patterns | Vít Jelínek, Stanislav Kučera | new03 |
| 1803.05943v1 | 2018-03-15 | Closed form expressions for Appell polynomials | José A. Adell, Alberto Lekuona | t26a |
| 1803.04547v2 | 2018-03-12 | Analysis of spectral clustering algorithms for community detection: the general bipartite setting | Zhixin Zhou, Arash A. Amini | new03 |
| 1712.10072v3 | 2017-12-28 | On the Intriguing Problem of Counting (n+1,n+2)-Core Partitions into Odd Parts | Anthony Zaleski, Doron Zeilberger | new02 |
| 1710.09769v2 | 2017-10-26 | Slopes of overconvergent Hilbert modular forms | Christopher Birkbeck | t39a |
| 1710.08566v1 | 2017-10-24 | Definite Sums of Hypergeometric Terms and Limits of P-Recursive Sequences | Hui Huang | new06 |
| 1710.07445v1 | 2017-10-20 | Univariate Contraction and Multivariate Desingularization of Ore Ideals | Yi Zhang | new06 |
| 1709.07290v3 | 2017-09-21 | Comparing the Switch and Curveball Markov Chains for Sampling Binary Matrices with Fixed Marginals | Corrie Jacobien Carstens, Pieter Kleer | new03 x04 |
| 1709.05051v1 | 2017-09-15 | Analytic Combinatorics in Several Variables: Effective Asymptotics and Lattice Path Enumeration | Stephen Melczer | new06 |
| 1708.07352v1 | 2017-08-24 | Structural Identifiability of Cyclic Graphical Models of Biological Networks with Latent Variables | Yulin Wang, Na Lu, Hongyu Miao | new03 |
| 1708.01421v1 | 2017-08-04 | On Generating functions of Diagonals Sequences of Sheffer and Riordan Number Triangles | Wolfdieter Lang | t41a |
| 1707.04801v2 | 2017-07-15 | Asymptotic formula of the number of Newton polygons | Shushi Harashita | t39a |
| 1707.04654v2 | 2017-07-14 | Automated Proofs of Many Conjectured Recurrences in the OEIS made by R.J. Mathar | Shalosh B. Ekhad, Mingjia Yang, Doron Zeilberger | new02 |
| 1703.03101v1 | 2017-03-09 | Robust MPC for tracking of nonholonomic robots with additive disturbances | Zhongqi Sun, Li Dai, Kun Liu, Yuanqing Xia 等 | new06 |
| 1702.06166v2 | 2017-02-20 | Bayesian Boolean Matrix Factorisation | Tammo Rukat, Chris C. Holmes, Michalis K. Titsias, Christopher Yau | new03 |
| 1702.06121v1 | 2017-02-20 | Reconstructing binary matrices under window constraints from their row and column sums | Andreas Alpers, Peter Gritzmann | new03 |
| 1702.04529v3 | 2017-02-15 | Semi-Baxter and strong-Baxter: two relatives of the Baxter sequence | Mathilde Bouvel, Veronica Guerrini, Andrew Rechnitzer, Simone Rinaldi | new06 |
| 1702.04177v2 | 2017-02-14 | Enumeration of Carlitz Multipermutations | Henrik Eriksson, Alexis Martin | new02 |
| 1701.07276v1 | 2017-01-25 | On the periodicity problem of residual r-Fubini sequences | Amir Abbas Asgari, Majid Jahangiri | t24a |
| 1701.00277v1 | 2017-01-01 | Self-Interference in Full-Duplex Multi-User MIMO Channels | Arman Shojaeifard, Kai-Kit Wong, Marco Di Renzo, Gan Zheng 等 | t26b |
| 1611.05901v3 | 2016-11-17 | D-finite Numbers | Hui Huang, Manuel Kauers | new06 |
| 1610.09806v2 | 2016-10-31 | The design of efficient algorithms for enumeration | Andrew R. Conway | x01 |
| 1609.04235v3 | 2016-09-14 | Efficient Removal Lemmas for Matrices | Noga Alon, Omri Ben-Eliezer | x04 |
| 1608.08245v1 | 2016-08-29 | An Exploration of Sequence A000975 | Paul K. Stockmeyer | new02 |
| 1608.05879v2 | 2016-08-21 | Noncrossing partitions for periodic braids | Eon-Kyung Lee, Sang-Jin Lee | x02 |
| 1607.07491v3 | 2016-07-25 | Better upper bounds on the Füredi-Hajnal limits of permutations | Josef Cibulka, Jan Kynčl | x04 |
| 1606.08718v4 | 2016-06-28 | Learning Nash Equilibrium for General-Sum Markov Games from Batch Data | Julien Pérolat, Florian Strub, Bilal Piot, Olivier Pietquin | t26b |
| 1606.07427v2 | 2016-06-23 | Special Values of Motivic $L$-Functions and Zeta-Polynomials for Symmetric Powers of Elliptic Curves | Steffen Löbrich, Wenjun Ma, Jesse Thorner | x02 |
| 1606.03159v1 | 2016-06-10 | Self-inversive polynomials, curves, and codes | David Joyner, Tony Shaska | x02 |
| 1605.05536v2 | 2016-05-18 | Explorations in the theory of partition zeta functions | Ken Ono, Larry Rolen, Robert Schneider | x02 |
| 1605.02038v2 | 2016-05-06 | Markov Chain methods for the bipartite Boolean quadratic programming problem | Daniel Karapetyan, Abraham P. Punnen, Andrew J. Parkes | new03 |
| 1604.04148v3 | 2016-04-14 | Efficient Counting of Degree Sequences | Kai Wang | new02 |
| 1604.01165v1 | 2016-04-05 | Quasi-classical generalized CRF structures | Izu Vaisman | new06 |
| 1602.06796v1 | 2016-02-22 | Counting distinct dimer hex tilings | Peter Taylor | new02 |
| 1602.05663v2 | 2016-02-18 | Endpoint estimates for one-dimensional oscillatory integral operator | Lechao Xiao | t39a |
| 1602.03364v1 | 2016-02-10 | Relations on words | Michel Rigo | x01 |
| 1602.00752v3 | 2016-02-02 | Zeta-polynomials for modular form periods | Ken Ono, Larry Rolen, Florian Sprung | x02 |
| 1602.00521v2 | 2016-02-01 | The Real-rootedness of Generalized Narayana Polynomials | Herman Z. Q. Chen, Arthur L. B. Yang, Philip B. Zhang | t13a |
| 1511.07922v8 | 2015-11-25 | Contraction of Ore Ideals with Applications | Yi Zhang | t39c |
| 1511.02527v3 | 2015-11-08 | Asymptotics of lattice walks via analytic combinatorics in several variables | Stephen Melczer, Mark C. Wilson | new06 |
| 1511.01699v2 | 2015-11-05 | Low Rank Approximation of Binary Matrices: Column Subset Selection and Generalizations | Chen Dan, Kristoffer Arnsfelt Hansen, He Jiang, Liwei Wang 等 | new03 |
| 1510.00027v2 | 2015-09-30 | Robust A Posteriori Error Estimation for Finite Element Approximation to H(curl) Problem | Zhiqiang Cai, Shuhao Cao, Rob Falgout | t26b |
| 1510.00075v2 | 2015-09-30 | Soliton resolution along a sequence of times with dispersive error for type II singular solutions to focusing energy critical wave equation | Hao Jia | t26b |
| 1509.08216v4 | 2015-09-28 | Fast Algorithms for Finding Pattern Avoiders and Counting Pattern Occurrences in Permutations | William Kuszmaul | new02 |
| 1509.04093v2 | 2015-09-14 | Sharp Oracle Inequalities for Square Root Regularization | Benjamin Stucky, Sara van de Geer | t26b |
| 1508.07637v2 | 2015-08-30 | Explicit Expressions for the Variance and Higher Moments of the Size of a Simultaneous Core Partition and its Limiting Distribution | Shalosh B. Ekhad, Doron Zeilberger | new02 |
| 1508.02608v1 | 2015-08-11 | Efficient Path Interpolation and Speed Profile Computation for Nonholonomic Mobile Robots | Stéphane Lens, Bernard Boigelot | new06 |
| 1507.08077v6 | 2015-07-29 | Functional error estimators for the adaptive discretization of inverse problems | Christian Clason, Barbara Kaltenbacher, Daniel Wachsmuth | t26b |
| 1506.03874v1 | 2015-06-11 | Extremal Functions of Forbidden Multidimensional Matrices | Jesse T. Geneson, Peter M. Tian | x01 |
| 1505.04616v5 | 2015-05-18 | Records for the number of distinct sites visited by a random walk on the fully-connected lattice | L. Turban | t24a |
| 1505.04065v2 | 2015-05-15 | Locating Patterns in the De Bruijn Torus | Victoria Horan, Brett Stevens | new03 |
| 1505.03125v3 | 2015-05-12 | Multidimensional Summation-By-Parts Operators: General Theory and Application to Simplex Elements | Jason E. Hicken, David C. Del Rey Fernández, David W. Zingg | t41a |
| 1503.08883v2 | 2015-03-31 | On a conjecture regarding primality of numbers constructed from prepending and appending identical digits | Chai Wah Wu | new02 |
| 1504.00212v4 | 2015-03-29 | New results on the stopping time behaviour of the Collatz 3x + 1 function | Mike Winkler | new02 |
| 1503.05658v3 | 2015-03-19 | An Extension of hibi's palindromic theorem | Daeseok Lee, Hyeong-Kwan Ju | new02 |
| 1503.00914v1 | 2015-03-03 | p-Ascent Sequences | Sergey Kitaev, Jeffrey Remmel | x01 |
| 1503.00289v1 | 2015-03-01 | Inverse spectral problem for GK integrable system | V. V. Fock | t39a |
| 1501.05095v2 | 2015-01-21 | Period integrals and mutation | Ketil Tveiten | t39a |
| 1412.6070v2 | 2014-12-18 | The asymptotic number of $12..d$-Avoiding Words with $r$ occurrences of each letter $1,2, ..., n$ | Guillaume Chapuy | new02 |
| 1412.2035v1 | 2014-12-05 | The Generating Functions Enumerating 12..d-Avoiding Words with r occurrences of each of 1,2, ... , n are D-finite for all d and all r | Shalosh B. Ekhad, Doron Zeilberger | new02 new06 |
| 1412.0345v2 | 2014-12-01 | Quadrant Marked Mesh Patterns and the r-Stirling Numbers | Matt Davis | t24a |
| 1411.0478v2 | 2014-11-03 | Trigonometric weight functions as K-theoretic stable envelope maps for the cotangent bundle of a flag variety | R. Rimanyi, V. Tarasov, A. Varchenko | t39a |
| 1408.1032v1 | 2014-08-04 | A case for Intranet-based 0nline portal for undergraduate Computer Science education | K. Viswanathan Iyer | new02 |
| 1405.3146v1 | 2014-05-13 | Enumeration of polyominoes defined in terms of pattern avoidance or convexity constraints | Daniela Battaglino | x01 |
| 1404.5573v2 | 2014-04-22 | Associated Lah numbers and r-Stirling numbers | Hacene Belbachir, Imad Eddine Bousbaa | t24a |
| 1403.5664v1 | 2014-03-22 | Automatic Proofs of Asymptotic ABNORMALITY (and much more!) of Natural Statistics Defined on Catalan-Counted Combinatorial Families | Shalosh B. Ekhad, Doron Zeilberger | new02 |
| 1402.3336v1 | 2014-02-13 | Permutation Patterns in Latin Squares | Michael J. Earnest, Samuel C. Gutekunst | x01 |
| 1401.6770v2 | 2014-01-27 | Edge states in 2D lattices with hopping anisotropy and Chebyshev polynomials | M. Eliashvili, G. I. Japaridze, G. Tsitsishvili, G. Tukhashvili | t41a |
| 1401.4739v1 | 2014-01-19 | Finding minimum Tucker submatrices | Jan Manuch, Arash Rafiey | x04 |
| 1401.2978v2 | 2014-01-13 | Scheduling Problems | Felix Breuer, Caroline J. Klivans | x02 |
| 1401.1532v1 | 2014-01-07 | An Explicit Conjectured Determinant Evaluation Whose Proof Would Make Me Happy (and the OEIS richer) | Doron Zeilberger | new02 |
| 1401.0224v1 | 2013-12-31 | Linear-Time Algorithms for Finding Tucker Submatrices and Lekkerkerker-Boland Subgraphs | Nathan Lindzey, Ross M. McConnell | new03 |
| 1312.0194v1 | 2013-12-01 | Some Combinatorial Problems on Binary Matrices in Programming Courses | Krasimir Yordzhev | new03 |
| 1310.5920v3 | 2013-10-19 | Diagonal recurrence relations for the Stirling numbers of the first kind | Feng Qi | t41a |
| 1310.4954v2 | 2013-10-18 | Compressed Vertical Partitioning for Full-In-Memory RDF Management | Sandra Álvarez-García, Nieves R. Brisaboa, Javier D. Fernández, Miguel A. Martínez-Prieto 等 | new03 |
| 1309.4237v2 | 2013-09-17 | Positivity properties of Jacobi-Stirling numbers and generalized Ramanujan polynomials | Zhicong Lin, Jiang Zeng | t41a |
| 1305.7066v1 | 2013-05-30 | A General Reciprocity Law for Symbols on Arbitrary Vector Spaces | Fernando Pablos Romo | t26b |
| 1304.4286v1 | 2013-04-15 | (a,b)-rectangle patterns in permutations and words | Sergey Kitaev, Jeffrey Remmel | new03 x01 |
| 1210.3684v2 | 2012-10-13 | Heuristic algorithms for the bipartite unconstrained 0-1 quadratic programming problem | Daniel Karapetyan, Abraham P. Punnen | new03 |
| 1208.0024v2 | 2012-07-31 | Parallelogram polyominoes, the sandpile model on a complete bipartite graph, and a q,t-Narayana polynomial | Mark Dukes, Yvan Le Borgne | t13a |
| 1207.1511v1 | 2012-07-06 | Random Distances Associated With Equilateral Triangles | Yanyan Zhuang, Jianping Pan | t41a |
| 1206.5178v1 | 2012-06-22 | Full support of the Kasteleyn operator associated with a bipartite toroidal graph | Álvar Ibeas Martín | t39a |
| 1206.1837v2 | 2012-06-08 | Efficient Algorithms for Finding Tucker Patterns | Cedric Chauve, Tamon Stephen, Maria Tamayo | new03 |
| 1205.3300v3 | 2012-05-15 | Non-D-finite excursions in the quarter plane | Alin Bostan, Kilian Raschel, Bruno Salvy | new06 |
| 1203.1446v1 | 2012-03-07 | A generic Hopf algebra for quantum statistical mechanics | Allan I. Solomon, Gerard E. H. Duchamp, Pawel Blasiak, Andrzej Horzela 等 | new04 x03 |
| 1202.4183v1 | 2012-02-19 | Families of Artin-Schreier curves with Cartier-Manin matrix of constant rank | Shawn Farnell, Rachel Pries | t39a |
| 1202.1203v3 | 2012-02-06 | A probabilistic interpretation of a sequence related to Narayana polynomials | T. Amdeberhan, V. H. Moll, C. Vignat | t13a |
| 1201.3135v2 | 2012-01-15 | Bargmann type estimates of the counting function for general Schrödinger operators | S. Molchanov, B. Vainberg | t39b |
| 1201.0622v2 | 2012-01-03 | Jacobi-Stirling polynomials and $P$-partitions | Ira M. Gessel, Zhicong Lin, Jiang Zeng | t41a |
| 1111.3088v3 | 2011-11-14 | The number of bar{3}bar{1}542-avoiding permutations | David Callan | new02 |
| 1107.1462v2 | 2011-07-07 | Single jet and prompt-photon inclusive production with multi-Regge kinematics: From Tevatron to LHC | B. A. Kniehl, V. A. Saleev, A. V. Shipilova, E. V. Yatsenko | new04 x03 |
| 1105.0937v2 | 2011-05-04 | On negative eigenvalues of low-dimensional Schrödinger operators | S. Molchanov, B. Vainberg | t39b |
| 1103.2285v1 | 2011-03-11 | Asymptotics for a Variant of the Mittag-Leffler Function | Stefan Gerhold | new06 |
| 1101.1666v1 | 2011-01-09 | Monotone triangles and 312 Pattern Avoidance | Arvind Ayyer, Robert Cori, Dominique Gouyou-Beauchamps | x01 |
| 1011.3131v1 | 2010-11-13 | Inclusive jet production at Tevatron in the Regge limit of QCD | V. A. Saleev, A. V. Shipilova, E. V. Yatsenko | new04 x03 |
| 1009.5828v1 | 2010-09-29 | Stellar intensity interferometry: Optimizing air Cherenkov telescope array layouts | Hannes Jensen, Dainis Dravins, Stephan LeBohec, Paul D. Nuñez | x01 |
| 1009.3985v1 | 2010-09-21 | Disquisitiones Arithmeticae and online sequence A108345 | Paul Monsky | new02 |
| 1005.1156v3 | 2010-05-07 | A new computational approach to ideal theory in number fields | Jordi Guardia, Jesus Montes, Enric Nart | t39a |
| 0911.5517v1 | 2009-11-30 | Diphoton production at Tevatron in the quasi-multi-Regge-kinematics approach | V. A. Saleev | new04 x03 |
| 0908.2641v4 | 2009-08-18 | Chain enumeration of $k$-divisible noncrossing partitions of classical types | Jang Soo Kim | x02 |
| 0907.0401v1 | 2009-07-02 | Refined enumerations of alternating sign matrices: monotone (d,m)-trapezoids with prescribed top and bottom row | Ilse Fischer | t41a |
| 0904.2761v1 | 2009-04-17 | A Non-Holonomic Systems Approach to Special Function Identities | Frédéric Chyzak, Manuel Kauers, Bruno Salvy | new04 |
| 0901.4665v4 | 2009-01-29 | Moment inversion problem for piecewise D-finite functions | Dmitry Batenkov | new06 |
| 0812.1193v2 | 2008-12-05 | Some Applications of the Fractional Poisson Probability Distribution | Nick Laskin | t41a |
| 0806.0666v4 | 2008-06-04 | (2+2)-free posets, ascent sequences and pattern avoiding permutations | Mireille Bousquet-Mélou, Anders Claesson, Mark Dukes, Sergey Kitaev | new06 |
| 0806.0434v2 | 2008-06-03 | Circular Peaks and Hilbert Series | Pierre Bouchard, Jun Ma, Yeong-Nan Yeh | x02 |
| 0805.2128v1 | 2008-05-14 | Eight Hateful Sequences | N. J. A. Sloane | new02 |
| 0802.3889v1 | 2008-02-26 | Polygones de Newton de certaines sommes de caractères et séries de Poincaré | R. Blache | t39a |
| 0802.1696v1 | 2008-02-12 | First Observations on Prefab Posets Whitney Numbers | A. Krzysztof Kwaśniewski | new05 |
| 0802.1382v1 | 2008-02-11 | New type Stirling like numbers - an email style letter | A. K. Kwasniewski | new05 |
| 0802.1162v1 | 2008-02-08 | Approximate substitutions and the normal ordering problem | H. Cheballah, G. H. E. Duchamp, K. A. Penson | new04 x03 |
| 0708.2212v2 | 2007-08-16 | Enumerative Properties of NC^B(p,q) | I. P. Goulden, Alexandru Nica, Ion Oancea | x02 |
| 0707.3711v1 | 2007-07-25 | Elliptic Gauss Sums and Hecke L-values at s=1 | Tetsuya Asai | t26b |
| 0707.2135v1 | 2007-07-14 | Nonconforming h-p spectral element methods for elliptic problems | P K Dutt, N Kishore Kumar, C S Upadhyay | t26b |
| 0705.3614v1 | 2007-05-24 | Bounding slopes of $p$-adic modular forms | Lawren Smithline | t39a |
| 0705.0032v1 | 2007-04-30 | Nonholonomic Algebroids, Finsler Geometry, and Lagrange-Hamilton Spaces | Sergiu I. Vacaru | new06 |
| math/0702817v1 | 2007-02-27 | Annihilating polynomials for quadratic forms and Stirling numbers of the second kind | Stefan A. G. De Wannemacker | new04 x03 |
| quant-ph/0701185v2 | 2007-01-25 | On the normal ordering of multi-mode boson operators | Toufik Mansour, Matthias Schork | new04 x03 |
| math/0701600v5 | 2007-01-22 | Random dense bipartite graphs and directed graphs with specified degrees | Catherine Greenhill, Brendan D. McKay | new03 |
| math/0611594v1 | 2006-11-20 | The Main Conjecture of Modular Towers and its higher rank generalization | Michael D. Fried | x06_fried |
| math/0510027v1 | 2005-10-03 | Prefab posets` Whitney numbers | A. K. Kwasniewski | new05 |
| quant-ph/0507206v2 | 2005-07-21 | Combinatorics of boson normal ordering and some applications | P. Blasiak | new04 x03 |
| quant-ph/0505180v1 | 2005-05-24 | Combinatorial approach to generalized Bell and Stirling numbers and boson normal ordering problem | M A Mendez, P Blasiak, K A Penson | new04 x03 |
| quant-ph/0402027v1 | 2004-02-03 | The general boson normal ordering problem | Pawel Blasiak, Karol A. Penson, Allan I. Solomon | new04 x03 |
| math/0309135v2 | 2003-09-07 | Aztec Diamonds and Baxter Permutations | Hal Canary | x01 |
| quant-ph/0304094v2 | 2003-04-13 | A New Symmetric Expression of Weyl Ordering | Kazuyuki Fujii, Tatsuo Suzuki | new04 x03 |
| math/0204269v1 | 2002-04-22 | Estimates for Oscillatory Integral Operators | Vyacheslav S. Rychkov | t39a |
| math/9910119v1 | 1999-10-22 | On elliptic operator pencils with general boundary conditions | R. Denk, R. Mennicken, L. Volevich | t39a |
| math/9907102v1 | 1999-07-15 | Boundary value problems for a class of elliptic operator pencils | R. Denk, R. Mennicken, L. Volevich | t39a |
