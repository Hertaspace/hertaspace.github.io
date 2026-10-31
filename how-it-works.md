---
title: How it works
date: 2026-10-31
tag: Background
keywords: surface code, minimum-weight perfect matching, MWPM, spacetime decoding, measurement errors, quantum error correction
summary: The dark background of this site is a simulation, not a canned animation. It runs a planar surface code with bit-flip, phase-flip and measurement errors, and decodes it round by round with minimum-weight perfect matching in spacetime.
---

## What you are seeing

The surface code stores quantum information in qubits on a lattice, and repeatedly measures parity checks that reveal errors without reading the stored information. Here every qubit can suffer a random X, Y or Z error, and each check can also report the wrong value.

- **Green and violet lines** are bit-flip and phase-flip errors that have not been corrected yet. The two kinds live on two interlaced lattices and are decoded separately.
- **Squares and diamonds** are detection events: places where the reading of a check changed between two rounds. Squares sit on the bit-flip lattice and diamonds on the phase-flip lattice. An event can come from a real error or from a misread check. The deeper the colour, the longer the event has waited.
- **Dashed curves** are nearby alternatives, the **thin solid curve** is the chosen pair, and the **thick cream path** is the correction.
- **Rings** mark what the decoder takes for a misread check: two events at one check, paired in time, so that no qubit needs fixing. At the rates used here, more than 98% of the rings are real misreads.

## How the decoder works

An error chain lights up detection events only at its two ends, so the decoder has to guess which events belong together. Minimum-weight perfect matching picks the pairing with the smallest total length, on the assumption that short chains are more likely than long ones. Events may also pair with a boundary of the lattice.

Distance is counted in space and in time, so a single misread check, which produces two events at the same place, is explained by a short step in time.

Each round, matching is solved exactly for the events still open, with Edmonds' blossom algorithm in plain JavaScript in your browser. A pair is committed only once both of its events are at least two rounds old, and later rounds cannot undo it. Most pairs are committed after two rounds.

The growing diamonds are a picture of this search, and they are illustrative. The pairing has already been computed when they appear. Their size comes from the spatial distance of the pair: half of it for two events, all of it for an event matched to a boundary. The regions of the real algorithm can merge and need not stay symmetric.

## Controls

Press **Hide text** in the dark theme to open the full-screen demo. There you can set the error rates and the round length, pause, and hold the left mouse button on the 2D lattice to disturb qubits. The ripple that follows the pointer is only a visual effect. The **3D**, **Time** and **Side** views show the same pattern with time as an extra direction, and the octahedra in those views are the spacetime version of the diamonds.

| Setting | While reading | Full screen |
|---|---|---|
| Error rate per qubit per round | 0.4% | 1%, adjustable |
| Misread rate per check per round | 0.3% | 0.67%, adjustable |
| Round length | 1 s | 0.75 s, adjustable |

Each error is a random X, Y or Z, so each lattice sees two thirds of that rate.

## Is it correct?

A background can be wrong without anyone noticing, so the decoder was tested on its own. The matching agreed with brute-force enumeration on 37,600 random graphs, and the version with boundaries agreed on 4,000 more.

The threshold test uses the same matching on one lattice, decoding a whole block at once rather than streaming as on screen. With bit flips and misreads at the same rate \(p\), and as many rounds as the code distance, logical failure rates behave as a threshold requires, with curves crossing near 3%. Wang, Harrington and Preskill report that the method succeeds below about 2.9% for this noise model ([arXiv:quant-ph/0207088](https://arxiv.org/abs/quant-ph/0207088)).

| Distance | \(p = 2\%\) | \(p = 3\%\) | \(p = 4\%\) |
|---|---|---|---|
| 5 | 0.031 | 0.087 | 0.177 |
| 7 | 0.012 | 0.072 | 0.228 |
| 9 | 0.006 | 0.100 | 0.256 |

These runs are small, so the crossing is only approximate. For the streaming decoder, the parity of its logical failure count was checked against an independent record of every error and correction, and they agreed in every episode.

## What it leaves out

This is a demonstration, not a research simulator.

- Measurement errors are modelled directly, with no gate-level circuit underneath.
- Weights are plain lattice distances, not derived from error probabilities.
- X and Z errors are decoded separately, so the correlation in a Y error is ignored.
- Only Pauli errors are tracked, classically. No quantum state is simulated.
- The decoder streams, so its pairs are never revisited. To stay real-time, each round considers at most 110 events per lattice from a window of eight rounds, oldest first. The result is therefore not the global optimum for the whole run.
- At the top of the sliders the decoder falls behind, and several hundred events stay open.

## Source

The code, the tests and a standalone demo are on GitHub at [Hertaspace/live-surface-code](https://github.com/Hertaspace/live-surface-code), under the Apache License 2.0.
