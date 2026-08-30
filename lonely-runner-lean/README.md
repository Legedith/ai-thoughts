# Lean 4 finite core for correlated-amplitude Riesz products

This package formalizes the finite, hypothesis-transparent part of an exploratory
Lonely Runner method:

- the bounded affine amplitude `amplitude s h`;
- exact mixed-second-moment cancellation from centred variables with covariance
  `-1 / s²`;
- the scalar square-root obstruction;
- pullback of pair cancellation through a coloring injective on every designated
  relation support;
- pointwise nonnegativity of the associated Riesz factors and finite products.

It does **not** claim a proof of the Lonely Runner Conjecture or of the proposed
asymptotic chromatic Riesz estimate. Those require Fourier-analytic and
additive-combinatorial lemmas not encoded here.

Pinned versions: Lean 4.33.1 and Mathlib v4.33.1.
