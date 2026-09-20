import H0mework.Realization.Faces.P713

/-!
# Proposition 714: the seven-symbol formula projects to saturation

P713 packages the affine relaxation ontology spine:

`X -> X + sigma * (T - X)`.

This file welds that spine back to the original saturation/noisy-OR language.
The two decisive projections are:

* `T = 1`: affine relaxation is exactly `bumpSatField`;
* `T = 0`: affine relaxation is exactly keep/residual scaling.

Thus state relaxation, salience bumping, and rate composition are not parallel
metaphors.  They are the same affine grammar read in different coordinates.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Target-one projection: saturation / bumping -/

/-- THEOREM 1: target-one affine relaxation is exactly the saturation bump. -/
theorem oneTarget_relaxModule_eq_bumpSatField
    (h ρ : K) :
    relaxModule (1 : K) ρ h = bumpSatField h ρ := by
  unfold relaxModule bumpSatField
  ring

/-- THEOREM 2: rate composition is target-one relaxation on the rate
coordinate itself. -/
theorem satOrField_eq_oneTarget_relaxModule
    (ρ₁ ρ₂ : K) :
    satOrField ρ₁ ρ₂ = relaxModule (1 : K) ρ₂ ρ₁ := by
  rw [oneTarget_relaxModule_eq_bumpSatField]
  unfold satOrField bumpSatField
  ring

/-- THEOREM 3: the target-one residual is the old headroom times the keep
rate. -/
theorem oneTarget_relaxModule_residual_mul
    (h ρ : K) :
    1 - relaxModule (1 : K) ρ h = (1 - h) * (1 - ρ) := by
  unfold relaxModule
  ring

/-- THEOREM 4: same-target affine composition at target one is exactly the
usual bumpSat/noisy-OR composition law. -/
theorem oneTarget_relaxModule_compose_eq_bumpSatField_satOr
    (h ρ₁ ρ₂ : K) :
    relaxModule (1 : K) ρ₂ (relaxModule (1 : K) ρ₁ h) =
      bumpSatField h (satOrField ρ₁ ρ₂) := by
  rw [relaxModule_compose]
  rw [oneTarget_relaxModule_eq_bumpSatField]

/-! ## Target-zero projection: keep / residual powers -/

/-- THEOREM 5: target-zero affine relaxation is exactly keep scaling. -/
theorem zeroTarget_relaxModule_eq_keep_mul
    (x ρ : K) :
    relaxModule (0 : K) ρ x = (1 - ρ) * x := by
  unfold relaxModule
  ring

/-- THEOREM 6: iterating target-zero relaxation produces the keep power. -/
theorem zeroTarget_relaxModule_iterate_eq_keep_pow
    (x σ : K) (n : ℕ) :
    (fun y : K => relaxModule (0 : K) σ y)^[n] x =
      ((1 - σ) ^ n) * x := by
  rw [relaxModule_iterate_eq_closed]
  simp

/-! ## The projection certificate -/

/-- P714 certificate: the P713 ontology spine, read through its target-one and
target-zero projections, is exactly the saturation / keep-power algebra. -/
structure SevenSymbolSaturationProjectionCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  ontology :
    SevenSymbolOntologySpineCertificate (K := K) (E := K) σ hσ0 hσ1
  target_one_is_bump :
    ∀ h ρ : K,
      relaxModule (1 : K) ρ h = bumpSatField h ρ
  rate_composition_is_target_one :
    ∀ ρ₁ ρ₂ : K,
      satOrField ρ₁ ρ₂ = relaxModule (1 : K) ρ₂ ρ₁
  target_one_residual :
    ∀ h ρ : K,
      1 - relaxModule (1 : K) ρ h = (1 - h) * (1 - ρ)
  target_one_composition :
    ∀ h ρ₁ ρ₂ : K,
      relaxModule (1 : K) ρ₂ (relaxModule (1 : K) ρ₁ h) =
        bumpSatField h (satOrField ρ₁ ρ₂)
  target_zero_is_keep :
    ∀ x ρ : K,
      relaxModule (0 : K) ρ x = (1 - ρ) * x
  target_zero_iterate :
    ∀ x : K, ∀ n : ℕ,
      (fun y : K => relaxModule (0 : K) σ y)^[n] x =
        ((1 - σ) ^ n) * x

/-- THEOREM 7: every active sigma carrier has the saturation-projection
certificate. -/
def sevenSymbolSaturationProjectionCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SevenSymbolSaturationProjectionCertificate σ hσ0 hσ1 where
  ontology := sevenSymbolOntologySpineCertificate σ hσ0 hσ1
  target_one_is_bump := oneTarget_relaxModule_eq_bumpSatField
  rate_composition_is_target_one := satOrField_eq_oneTarget_relaxModule
  target_one_residual := oneTarget_relaxModule_residual_mul
  target_one_composition := oneTarget_relaxModule_compose_eq_bumpSatField_satOr
  target_zero_is_keep := zeroTarget_relaxModule_eq_keep_mul
  target_zero_iterate := by
    intro x n
    exact zeroTarget_relaxModule_iterate_eq_keep_pow x σ n

end AffineRelaxation
end SaturationMonoid
