import H0mework.Computation.Phase.P722

/-!
# Proposition 723: complement-linear convex updates force bumpSat

P717 proved the coefficient-level uniqueness theorem for target-one
biaffine updates.  This file proves the sharper coordinate statement named in
the notes:

`complement -> linear -> convex combination -> bumpSat`.

In the headroom coordinate, a complement-linear target-one update is any update
whose remaining headroom after the step is a scalar multiple of the old
headroom:

`1 - f h sigma = keep sigma * (1 - h)`.

Once the empty-headroom state reads out the update rate (`f 0 sigma = sigma`),
the keep factor is forced to be `1 - sigma`; hence the update is exactly

`f h sigma = 1 - (1 - sigma) * (1 - h) = bumpSatField h sigma`.

Thus the convex-combination face is not an extra modeling choice.  It is the
unique target-one update compatible with complement-linear headroom transport
and the rate readout.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u

variable {K : Type u} [Field K]

/-! ## Complement-linear target-one updates -/

/-- A target-one update is complement-linear when it transports the remaining
headroom by multiplying it by a rate-dependent keep factor. -/
def IsComplementLinearTargetOneUpdate (f : K -> K -> K) : Prop :=
  ∃ keep : K -> K, ∀ h sigma : K,
    1 - f h sigma = keep sigma * (1 - h)

/-- THEOREM 1: for a complement-linear target-one update, the empty-state rate
readout forces the keep factor to be exactly `1 - sigma`. -/
theorem complementLinear_keepFactor_forced
    (f : K -> K -> K) (keep : K -> K)
    (hkeep : ∀ h sigma : K, 1 - f h sigma = keep sigma * (1 - h))
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
    ∀ sigma : K, keep sigma = 1 - sigma := by
  intro sigma
  have h0 := hkeep 0 sigma
  rw [hrate sigma] at h0
  simpa using h0.symm

/-- THEOREM 2: complement-linearity plus empty-state rate readout force the
full complement residual law. -/
theorem complementResidualLaw_of_complementLinear_rateReadout
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
    ∀ h sigma : K, 1 - f h sigma = (1 - sigma) * (1 - h) := by
  rcases hlin with ⟨keep, hkeep⟩
  intro h sigma
  rw [hkeep h sigma,
    complementLinear_keepFactor_forced f keep hkeep hrate sigma]

/-- THEOREM 3: complement-linearity plus empty-state rate readout make
`bumpSatField` the unique target-one update. -/
theorem bumpSat_unique_of_complementLinear_rateReadout
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
    ∀ h sigma : K, f h sigma = bumpSatField h sigma := by
  intro h sigma
  have hres :=
    complementResidualLaw_of_complementLinear_rateReadout f hlin hrate h sigma
  calc
    f h sigma = 1 - (1 - f h sigma) := by ring
    _ = 1 - ((1 - sigma) * (1 - h)) := by rw [hres]
    _ = bumpSatField h sigma := by
      unfold bumpSatField
      ring

/-! ## Forced convex-combination face -/

/-- THEOREM 4: the forced update is the convex target-one combination
`(1-sigma) * h + sigma`. -/
theorem complementLinear_forced_convex_combination
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
    ∀ h sigma : K,
      f h sigma = (1 - sigma) * h + sigma := by
  intro h sigma
  rw [bumpSat_unique_of_complementLinear_rateReadout f hlin hrate]
  unfold bumpSatField
  ring

/-- THEOREM 5: the identity start is forced; rate `0` is a no-op. -/
theorem complementLinear_forced_identity_start
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
  ∀ h : K, f h 0 = h := by
  intro h
  rw [bumpSat_unique_of_complementLinear_rateReadout f hlin hrate]
  unfold bumpSatField
  ring

/-- THEOREM 6: the absorbing target endpoint is forced. -/
theorem complementLinear_forced_absorbing_target
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma) :
    ∀ sigma : K, f 1 sigma = 1 := by
  intro sigma
  rw [bumpSat_unique_of_complementLinear_rateReadout f hlin hrate]
  unfold bumpSatField
  ring

/-! ## Forced interval closure -/

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 7: on the active unit interval, the unique complement-linear
update is closed on `[0,1]`. -/
theorem complementLinear_forced_interval_closure
    (f : K -> K -> K)
    (hlin : IsComplementLinearTargetOneUpdate f)
    (hrate : ∀ sigma : K, f 0 sigma = sigma)
    (h sigma : K)
    (hh0 : 0 <= h) (hh1 : h <= 1)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    0 <= f h sigma ∧ f h sigma <= 1 := by
  rw [bumpSat_unique_of_complementLinear_rateReadout f hlin hrate]
  exact bumpSatField_mem_Icc h sigma hh0 hh1 hs0 hs1

/-! ## Certificate -/

/-- P723 certificate: complement-linear headroom transport plus empty-state
rate readout uniquely force the convex target-one update, namely
`bumpSatField`. -/
structure ComplementLinearBumpSatFinalUniquenessCertificate
    (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop where
  keep_factor_forced :
    ∀ (f : K -> K -> K) (keep : K -> K),
      (∀ h sigma : K, 1 - f h sigma = keep sigma * (1 - h)) ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ sigma : K, keep sigma = 1 - sigma
  complement_residual_law_forced :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ h sigma : K, 1 - f h sigma = (1 - sigma) * (1 - h)
  update_unique :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ h sigma : K, f h sigma = bumpSatField h sigma
  convex_combination_forced :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ h sigma : K, f h sigma = (1 - sigma) * h + sigma
  identity_start_forced :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ h : K, f h 0 = h
  absorbing_target_forced :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ sigma : K, f 1 sigma = 1
  interval_closure_forced :
    ∀ f : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      ∀ h sigma : K,
        0 <= h -> h <= 1 -> 0 <= sigma -> sigma <= 1 ->
        0 <= f h sigma ∧ f h sigma <= 1

/-- THEOREM 8: every linear ordered field carries the final target-one
`bumpSat` uniqueness certificate. -/
theorem complementLinearBumpSatFinalUniquenessCertificate :
    ComplementLinearBumpSatFinalUniquenessCertificate K where
  keep_factor_forced := complementLinear_keepFactor_forced
  complement_residual_law_forced :=
    complementResidualLaw_of_complementLinear_rateReadout
  update_unique := bumpSat_unique_of_complementLinear_rateReadout
  convex_combination_forced := complementLinear_forced_convex_combination
  identity_start_forced := complementLinear_forced_identity_start
  absorbing_target_forced := complementLinear_forced_absorbing_target
  interval_closure_forced := complementLinear_forced_interval_closure

end AffineRelaxation
end SaturationMonoid
