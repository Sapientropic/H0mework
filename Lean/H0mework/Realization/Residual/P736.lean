import H0mework.Realization.Residual.P735

/-!
# Proposition 736: residual split uniqueness

P735 proves the conservative root:

`r = keep r + trace r`.

This file closes the next throat.  On the scalar carrier, if the trace side is
linear in the residual and its unit-residual readout is the rate `sigma`, then
the split is forced:

`trace sigma r = sigma * r`

`keep sigma r = (1-sigma) * r`.

Thus `r = (1-sigma)r + sigma r` is not a chosen presentation.  It is the unique
scalar residual conservation split compatible with linear trace and rate
readout.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

variable {K : Type u} [Field K]

/-- A scalar residual conservation split whose trace is linear in the residual
and whose unit-residual readout is the rate. -/
structure IsScalarResidualConservationSplit
    (keep trace : K -> K -> K) : Prop where
  conserve : ∀ sigma r : K, r = keep sigma r + trace sigma r
  trace_linear : ∀ sigma r : K, trace sigma r = trace sigma 1 * r
  rate_readout : ∀ sigma : K, trace sigma 1 = sigma

/-- THEOREM 1: trace linearity plus rate readout forces the trace side to be
`sigma * r`. -/
theorem scalarResidualSplit_trace_forced
    {keep trace : K -> K -> K}
    (h : IsScalarResidualConservationSplit keep trace)
    (sigma r : K) :
    trace sigma r =
      scalarTrace (K := K) (E := K) sigma r := by
  rw [h.trace_linear sigma r, h.rate_readout sigma]
  unfold scalarTrace
  simp

/-- THEOREM 2: conservation then forces the keep side to be `(1-sigma) * r`. -/
theorem scalarResidualSplit_keep_forced
    {keep trace : K -> K -> K}
    (h : IsScalarResidualConservationSplit keep trace)
    (sigma r : K) :
    keep sigma r =
      scalarKeep (K := K) (E := K) sigma r := by
  have htrace := scalarResidualSplit_trace_forced h sigma r
  have hconserve := h.conserve sigma r
  calc
    keep sigma r = keep sigma r + trace sigma r - trace sigma r := by ring
    _ = r - trace sigma r := by rw [← hconserve]
    _ = r - scalarTrace (K := K) (E := K) sigma r := by rw [htrace]
    _ = scalarKeep (K := K) (E := K) sigma r := by
      unfold scalarKeep scalarTrace
      simp
      ring

/-- THEOREM 3: the scalar split laws are equivalent to the canonical scalar
keep/trace pair. -/
theorem scalarResidualConservationSplit_iff_canonical
    (keep trace : K -> K -> K) :
    IsScalarResidualConservationSplit keep trace ↔
      (∀ sigma r : K,
        keep sigma r = scalarKeep (K := K) (E := K) sigma r ∧
        trace sigma r = scalarTrace (K := K) (E := K) sigma r) := by
  constructor
  · intro h sigma r
    exact ⟨scalarResidualSplit_keep_forced h sigma r,
      scalarResidualSplit_trace_forced h sigma r⟩
  · intro h
    constructor
    · intro sigma r
      rw [(h sigma r).1, (h sigma r).2]
      exact scalarKeep_scalarTrace_conserve (K := K) (E := K) sigma r
    · intro sigma r
      rw [(h sigma r).2, (h sigma 1).2]
      unfold scalarTrace
      simp
    · intro sigma
      rw [(h sigma 1).2]
      unfold scalarTrace
      simp

/-- THEOREM 4: two accepted scalar residual splits are extensionally equal on
both keep and trace. -/
theorem scalarResidualConservationSplit_extensional_unique
    {keep₁ trace₁ keep₂ trace₂ : K -> K -> K}
    (h₁ : IsScalarResidualConservationSplit keep₁ trace₁)
    (h₂ : IsScalarResidualConservationSplit keep₂ trace₂) :
    keep₁ = keep₂ ∧ trace₁ = trace₂ := by
  constructor
  · funext sigma r
    rw [scalarResidualSplit_keep_forced h₁ sigma r,
      scalarResidualSplit_keep_forced h₂ sigma r]
  · funext sigma r
    rw [scalarResidualSplit_trace_forced h₁ sigma r,
      scalarResidualSplit_trace_forced h₂ sigma r]

/-- THEOREM 5: the affine display of any accepted scalar split is forced to be
`relaxTo`. -/
theorem scalarResidualSplit_affine_display_forced_relaxTo
    {keep trace : K -> K -> K}
    (h : IsScalarResidualConservationSplit keep trace)
    (target sigma x : K) :
    x + trace sigma (target - x) =
      relaxTo target sigma x := by
  rw [scalarResidualSplit_trace_forced h sigma (target - x)]
  exact residualSplit_scalar_affine_trace_display_eq_relaxModule
    (K := K) (E := K) target x sigma

/-- THEOREM 6: the residual-transport display of any accepted scalar split is
forced to be `relaxModule`. -/
theorem scalarResidualSplit_transport_display_forced_relaxModule
    {keep trace : K -> K -> K}
    (h : IsScalarResidualConservationSplit keep trace)
    (target sigma x : K) :
    residualTransportUpdate (keep sigma) target x =
      relaxModule target sigma x := by
  rw [funext (scalarResidualSplit_keep_forced h sigma)]
  exact residualTransportUpdate_scalarKeep_eq_relaxModule
    (K := K) (E := K) target x sigma

/-- THEOREM 7: at target one, any accepted scalar split is forced to be
`bumpSatField`. -/
theorem scalarResidualSplit_targetOne_display_forced_bumpSat
    {keep trace : K -> K -> K}
    (h : IsScalarResidualConservationSplit keep trace)
    (sigma x : K) :
    x + trace sigma (1 - x) =
      bumpSatField x sigma := by
  rw [scalarResidualSplit_trace_forced h sigma (1 - x)]
  exact residualSplit_targetOne_trace_display_eq_bumpSat
    (K := K) x sigma

/-- P736 certificate: the scalar residual conservation split is unique, and
all of its transport / affine / target-one readings are forced. -/
structure ResidualConservationSplitUniquenessCertificate
    (K : Type u) [Field K] : Prop where
  trace_forced :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ->
        ∀ sigma r : K,
          trace sigma r =
            scalarTrace (K := K) (E := K) sigma r
  keep_forced :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ->
        ∀ sigma r : K,
          keep sigma r =
            scalarKeep (K := K) (E := K) sigma r
  iff_canonical :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ↔
        (∀ sigma r : K,
          keep sigma r = scalarKeep (K := K) (E := K) sigma r ∧
          trace sigma r = scalarTrace (K := K) (E := K) sigma r)
  extensional_unique :
    ∀ keep₁ trace₁ keep₂ trace₂ : K -> K -> K,
      IsScalarResidualConservationSplit keep₁ trace₁ ->
      IsScalarResidualConservationSplit keep₂ trace₂ ->
        keep₁ = keep₂ ∧ trace₁ = trace₂
  affine_display_forced_relaxTo :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ->
        ∀ target sigma x : K,
          x + trace sigma (target - x) =
            relaxTo target sigma x
  transport_display_forced_relaxModule :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ->
        ∀ target sigma x : K,
          residualTransportUpdate (keep sigma) target x =
            relaxModule target sigma x
  target_one_display_forced_bumpSat :
    ∀ keep trace : K -> K -> K,
      IsScalarResidualConservationSplit keep trace ->
        ∀ sigma x : K,
          x + trace sigma (1 - x) =
            bumpSatField x sigma
  residual_conservation_split :
    ResidualConservationSplitCertificate K K

/-- THEOREM 8: the scalar residual conservation split uniqueness certificate.
-/
theorem residualConservationSplitUniquenessCertificate :
    ResidualConservationSplitUniquenessCertificate K where
  trace_forced := by
    intro keep trace h sigma r
    exact scalarResidualSplit_trace_forced h sigma r
  keep_forced := by
    intro keep trace h sigma r
    exact scalarResidualSplit_keep_forced h sigma r
  iff_canonical :=
    scalarResidualConservationSplit_iff_canonical
  extensional_unique := by
    intro keep₁ trace₁ keep₂ trace₂ h₁ h₂
    exact scalarResidualConservationSplit_extensional_unique h₁ h₂
  affine_display_forced_relaxTo := by
    intro keep trace h target sigma x
    exact scalarResidualSplit_affine_display_forced_relaxTo h target sigma x
  transport_display_forced_relaxModule := by
    intro keep trace h target sigma x
    exact scalarResidualSplit_transport_display_forced_relaxModule h target sigma x
  target_one_display_forced_bumpSat := by
    intro keep trace h sigma x
    exact scalarResidualSplit_targetOne_display_forced_bumpSat h sigma x
  residual_conservation_split :=
    residualConservationSplitCertificate

end AffineRelaxation
end SaturationMonoid
