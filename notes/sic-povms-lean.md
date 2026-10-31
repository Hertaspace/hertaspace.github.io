---
title: SIC-POVMs in every dimension, formalized in Lean 4
date: 2026-10-25
tag: Formalized
keywords: SIC-POVM, Zauner's conjecture, Lean 4, formal verification, quantum information
summary: A machine-checked Lean 4 proof that SIC-POVMs exist in every finite dimension, the existence part of Zauner's conjecture. It follows the proof of Radchenko and Wheeler, with a theorem of Appleby, Flammia and Kopp. Written by AI agents under human direction. Accepted by six kernels.
source: https://github.com/Hertaspace/sic-povm-lean
source_label: Repository
cite: @misc{yang2026sicpovmlean,|  author       = {Yang, Yaoling},|  title        = {{SIC-POVMs} exist in every dimension: a {Lean} 4 formalization},|  year         = {2026},|  howpublished = {GitHub repository},|  url          = {https://github.com/Hertaspace/sic-povm-lean},|  note         = {Release v1.0}|}
---

## Statement

For every integer \(d \ge 1\) there exist \(d^2\) unit vectors \(\psi_i\) in \(\mathbb{C}^d\) with

$$ |\langle \psi_i, \psi_j \rangle|^2 = \frac{1}{d+1} \qquad \text{for all } i \neq j. $$

Such a family is the standard description of a symmetric informationally complete POVM (SIC-POVM). The statement is copied from Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures), where it is the existence formulation of Open Quantum Problem 23. The project also proves an analogue for rank-\(r\) SICs, whenever \(r \ge 1\), \(d > 2r + 1\) and \(r(d-r)\) divides \(d^2 - 1\).

## Credit

The mathematics is due to D. Radchenko and C. Wheeler ([arXiv:2609.21892](https://arxiv.org/abs/2609.21892v2)) and to M. Appleby, S. T. Flammia and G. S. Kopp ([arXiv:2501.03970](https://arxiv.org/abs/2501.03970)). Māris Ozols has an earlier, independent Lean 4 formalization of the same existence results, [marozols/SIC-existence](https://github.com/marozols/SIC-existence). The Lean code here was written by large language model agents under human direction.

## Checks

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, and six kernels accept it. The project has 443 files and about 110,000 lines of Lean, and it builds on Mathlib. The [repository](https://github.com/Hertaspace/sic-povm-lean) has the full proof outline, sources and verification records.
