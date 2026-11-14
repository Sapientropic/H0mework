import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.Proposition291

/-!
# Forgetting bridge track

Stable Lean entrypoint for the finite/continuous forgetting skeleton.

The key reusable bridge now has two layers:

* P229 proves the density-level gamma-Laplace identity.
* P230 connects that identity to Mathlib's `ProbabilityTheory.gammaMeasure`
  and to producer certificates of the form `HasLaw sampleRate (gammaMeasure ...)`.
* P291 adds the derivative-sign side at the positive-base coordinate:
  `x ↦ x^(-shape)` is completely monotone on `x > 0`, and the shifted-power
  time curve carries the same gamma-density Laplace witness.

Downstream empirical or runtime work should prove/import a concrete
producer certificate and then consume the P230 expectation theorem.  This module
does not assert that any real sampler, quadrature routine, or data stream has
gamma law, and it does not formalize the full abstract Bernstein theorem or
the affine-pullback derivative theorem for `t ↦ (1 + b*t)^(-c)`.
-/
