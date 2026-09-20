import H0mework.Realization.RelaxationAlgebra.P724
import H0mework.Realization.Relaxation.P730

/-!
# Proposition 731: final relaxation uniqueness throat

P723 proves the forward root:

`complement-linear headroom transport + rate readout -> bumpSat`.

P724 lifts it to target-general relaxation:

`target-chart complement transport + target-one rate readout -> relaxTo`.

This file closes the throat as equivalence, not just implication.  On the
target-one face, structural complement transport, residual multiplication,
convex-combination form, and `bumpSatField` are the same object.  On the
target-general scalar face, target-chart complement transport, target residual
multiplication, and `relaxTo` are the same object.

It also packages the extensional uniqueness statement: two updates satisfying
the same structural laws cannot differ.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u

variable {K : Type u} [Field K]

/-! ## Target-one equivalences -/

/-- THEOREM 1: a target-one update satisfies the structural
complement-linear/rate-readout laws iff it is exactly `bumpSatField`. -/
theorem targetOne_complementLinear_rateReadout_iff_bumpSat
    (f : K -> K -> K) :
    (IsComplementLinearTargetOneUpdate f ∧
        (∀ sigma : K, f 0 sigma = sigma)) ↔
      (∀ h sigma : K, f h sigma = bumpSatField h sigma) := by
  constructor
  · intro hstruct
    exact bumpSat_unique_of_complementLinear_rateReadout
      f hstruct.1 hstruct.2
  · intro hf
    constructor
    · refine ⟨fun sigma : K => 1 - sigma, ?_⟩
      intro h sigma
      rw [hf h sigma]
      unfold bumpSatField
      ring
    · intro sigma
      rw [hf 0 sigma]
      unfold bumpSatField
      ring

/-- THEOREM 2: the complement residual law is equivalent to `bumpSatField`. -/
theorem targetOne_residualLaw_iff_bumpSat
    (f : K -> K -> K) :
    (∀ h sigma : K, 1 - f h sigma = (1 - sigma) * (1 - h)) ↔
      (∀ h sigma : K, f h sigma = bumpSatField h sigma) := by
  constructor
  · intro hres h sigma
    calc
      f h sigma = 1 - (1 - f h sigma) := by ring
      _ = 1 - ((1 - sigma) * (1 - h)) := by rw [hres h sigma]
      _ = bumpSatField h sigma := by
        unfold bumpSatField
        ring
  · intro hf h sigma
    rw [hf h sigma]
    unfold bumpSatField
    ring

/-- THEOREM 3: the convex-combination target-one form is equivalent to
`bumpSatField`. -/
theorem targetOne_convexCombination_iff_bumpSat
    (f : K -> K -> K) :
    (∀ h sigma : K, f h sigma = (1 - sigma) * h + sigma) ↔
      (∀ h sigma : K, f h sigma = bumpSatField h sigma) := by
  constructor
  · intro hconv h sigma
    rw [hconv h sigma]
    unfold bumpSatField
    ring
  · intro hf h sigma
    rw [hf h sigma]
    unfold bumpSatField
    ring

/-- THEOREM 4: two structurally valid target-one updates are extensionally
equal.  There is no second complement-linear convex target-one update. -/
theorem targetOne_structural_updates_extensional_unique
    (f g : K -> K -> K)
    (hf : IsComplementLinearTargetOneUpdate f)
    (hg : IsComplementLinearTargetOneUpdate g)
    (hfrate : ∀ sigma : K, f 0 sigma = sigma)
    (hgrate : ∀ sigma : K, g 0 sigma = sigma) :
    f = g := by
  funext h sigma
  rw [bumpSat_unique_of_complementLinear_rateReadout f hf hfrate h sigma]
  rw [bumpSat_unique_of_complementLinear_rateReadout g hg hgrate h sigma]

/-! ## Target-general scalar equivalences -/

/-- THEOREM 5: a target-general scalar update satisfies target-chart
complement transport plus target-one rate readout iff it is exactly `relaxTo`.
-/
theorem targetGeneral_chart_rateReadout_iff_relaxTo
    (f : K -> K -> K -> K) :
    (IsTargetChartComplementLinearUpdate f ∧
        (∀ sigma : K, f 1 sigma 0 = sigma)) ↔
      (∀ target sigma x : K, f target sigma x = relaxTo target sigma x) := by
  constructor
  · intro hstruct
    exact relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hstruct.1 hstruct.2
  · intro hf
    constructor
    · refine ⟨fun sigma : K => 1 - sigma, ?_⟩
      intro target sigma x
      rw [hf target sigma x]
      exact target_sub_relaxTo target sigma x
    · intro sigma
      rw [hf 1 sigma 0]
      unfold relaxTo
      ring

/-- THEOREM 6: the target residual law is equivalent to `relaxTo`. -/
theorem targetGeneral_residualLaw_iff_relaxTo
    (f : K -> K -> K -> K) :
    (∀ target sigma x : K,
        target - f target sigma x = (1 - sigma) * (target - x)) ↔
      (∀ target sigma x : K, f target sigma x = relaxTo target sigma x) := by
  constructor
  · intro hres target sigma x
    calc
      f target sigma x = target - (target - f target sigma x) := by ring
      _ = target - ((1 - sigma) * (target - x)) := by
        rw [hres target sigma x]
      _ = relaxTo target sigma x := by
        unfold relaxTo
        ring
  · intro hf target sigma x
    rw [hf target sigma x]
    exact target_sub_relaxTo target sigma x

/-- THEOREM 7: the target-general convex-combination form is equivalent to
`relaxTo`. -/
theorem targetGeneral_convexCombination_iff_relaxTo
    (f : K -> K -> K -> K) :
    (∀ target sigma x : K,
        f target sigma x = (1 - sigma) * x + sigma * target) ↔
      (∀ target sigma x : K, f target sigma x = relaxTo target sigma x) := by
  constructor
  · intro hconv target sigma x
    rw [hconv target sigma x]
    rw [relaxTo_eq_convex]
  · intro hf target sigma x
    rw [hf target sigma x]
    rw [relaxTo_eq_convex]

/-- THEOREM 8: two structurally valid target-general scalar updates are
extensionally equal. -/
theorem targetGeneral_structural_updates_extensional_unique
    (f g : K -> K -> K -> K)
    (hf : IsTargetChartComplementLinearUpdate f)
    (hg : IsTargetChartComplementLinearUpdate g)
    (hfrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (hgrate : ∀ sigma : K, g 1 sigma 0 = sigma) :
    f = g := by
  funext target sigma x
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hf hfrate target sigma x]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      g hg hgrate target sigma x]

/-! ## Final certificate -/

/-- P731 certificate: complement transport, residual law, convex combination,
and the named `bumpSat`/`relaxTo` updates are the same scalar relaxation
object; extensional uniqueness rules out a second update. -/
structure FinalRelaxationUniquenessThroatCertificate
    (K : Type u) [Field K] : Prop where
  target_one_structural_iff_bumpSat :
    ∀ f : K -> K -> K,
      (IsComplementLinearTargetOneUpdate f ∧
          (∀ sigma : K, f 0 sigma = sigma)) ↔
        (∀ h sigma : K, f h sigma = bumpSatField h sigma)
  target_one_residual_iff_bumpSat :
    ∀ f : K -> K -> K,
      (∀ h sigma : K, 1 - f h sigma = (1 - sigma) * (1 - h)) ↔
        (∀ h sigma : K, f h sigma = bumpSatField h sigma)
  target_one_convex_iff_bumpSat :
    ∀ f : K -> K -> K,
      (∀ h sigma : K, f h sigma = (1 - sigma) * h + sigma) ↔
        (∀ h sigma : K, f h sigma = bumpSatField h sigma)
  target_one_extensional_unique :
    ∀ f g : K -> K -> K,
      IsComplementLinearTargetOneUpdate f ->
      IsComplementLinearTargetOneUpdate g ->
      (∀ sigma : K, f 0 sigma = sigma) ->
      (∀ sigma : K, g 0 sigma = sigma) ->
      f = g
  target_general_structural_iff_relaxTo :
    ∀ f : K -> K -> K -> K,
      (IsTargetChartComplementLinearUpdate f ∧
          (∀ sigma : K, f 1 sigma 0 = sigma)) ↔
        (∀ target sigma x : K, f target sigma x = relaxTo target sigma x)
  target_general_residual_iff_relaxTo :
    ∀ f : K -> K -> K -> K,
      (∀ target sigma x : K,
          target - f target sigma x = (1 - sigma) * (target - x)) ↔
        (∀ target sigma x : K, f target sigma x = relaxTo target sigma x)
  target_general_convex_iff_relaxTo :
    ∀ f : K -> K -> K -> K,
      (∀ target sigma x : K,
          f target sigma x = (1 - sigma) * x + sigma * target) ↔
        (∀ target sigma x : K, f target sigma x = relaxTo target sigma x)
  target_general_extensional_unique :
    ∀ f g : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      IsTargetChartComplementLinearUpdate g ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      (∀ sigma : K, g 1 sigma 0 = sigma) ->
      f = g

/-- THEOREM 9: every field carries the final scalar relaxation uniqueness
throat. -/
theorem finalRelaxationUniquenessThroatCertificate :
    FinalRelaxationUniquenessThroatCertificate K where
  target_one_structural_iff_bumpSat :=
    targetOne_complementLinear_rateReadout_iff_bumpSat
  target_one_residual_iff_bumpSat :=
    targetOne_residualLaw_iff_bumpSat
  target_one_convex_iff_bumpSat :=
    targetOne_convexCombination_iff_bumpSat
  target_one_extensional_unique :=
    targetOne_structural_updates_extensional_unique
  target_general_structural_iff_relaxTo :=
    targetGeneral_chart_rateReadout_iff_relaxTo
  target_general_residual_iff_relaxTo :=
    targetGeneral_residualLaw_iff_relaxTo
  target_general_convex_iff_relaxTo :=
    targetGeneral_convexCombination_iff_relaxTo
  target_general_extensional_unique :=
    targetGeneral_structural_updates_extensional_unique

end AffineRelaxation
end SaturationMonoid
