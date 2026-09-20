import H0mework.Realization.Residual.P716

/-!
# Proposition 717: bumpSat is the unique complement-linear target-one update

P713-P716 prove that the seven-symbol relaxation grammar projects to
saturation, continuous exponential relaxation, and finite gain/loss accounting.

This file closes the inverse direction: once an update is read on the
target-one face, the complement/residual law and the endpoint laws force the
update to be `bumpSatField`.  There is no second affine update hiding behind
the notation.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## Complement residual law forces bumpSat -/

/-- THEOREM 1: if an update consumes headroom by the complement residual law,
then it is exactly `bumpSatField`.

This is the sharp complement statement:

`1 - f h sigma = (1 - h) * (1 - sigma)`

already determines the target-one update. -/
theorem bumpSat_unique_of_complement_residual_law
    (f : ℝ -> ℝ -> ℝ)
    (hres : ∀ h σ : ℝ, 1 - f h σ = (1 - h) * (1 - σ)) :
    ∀ h σ : ℝ, f h σ = bumpSatField h σ := by
  intro h σ
  have hres' := hres h σ
  unfold bumpSatField
  nlinarith

/-! ## Biaffine endpoint laws force the complement residual law -/

/-- A target-one update is biaffine when it is affine in the two coordinates
with the single interaction term `h * sigma`. -/
def IsBiaffineUpdate (f : ℝ -> ℝ -> ℝ) : Prop :=
  ∃ A B C D : ℝ, ∀ h σ : ℝ,
    f h σ = A * (h * σ) + B * h + C * σ + D

/-- THEOREM 2: any biaffine update with the three target-one endpoint laws

* `sigma = 0` is identity,
* `h = 0` reads out the rate,
* `h = 1` is absorbing,

is exactly `bumpSatField`. -/
theorem bumpSat_unique_of_biaffine_endpoint_laws
    (f : ℝ -> ℝ -> ℝ)
    (hlin : IsBiaffineUpdate f)
    (hid : ∀ h : ℝ, f h 0 = h)
    (hrate : ∀ σ : ℝ, f 0 σ = σ)
    (habs : ∀ σ : ℝ, f 1 σ = 1) :
    ∀ h σ : ℝ, f h σ = bumpSatField h σ := by
  rcases hlin with ⟨A, B, C, D, hpoly⟩
  have hD : D = 0 := by
    have hpoly00 : f 0 0 = D := by
      simpa using hpoly 0 0
    have hrate0 : f 0 0 = 0 := hrate 0
    rw [← hpoly00, hrate0]
  have hB : B = 1 := by
    have hpoly10 : f 1 0 = B + D := by
      simpa [mul_assoc] using hpoly 1 0
    have hid1 : f 1 0 = 1 := hid 1
    have hBD : B + D = 1 := by
      rw [← hpoly10, hid1]
    rw [hD] at hBD
    simpa using hBD
  have hC : C = 1 := by
    have hpoly01 : f 0 1 = C + D := by
      simpa [mul_assoc] using hpoly 0 1
    have hrate1 : f 0 1 = 1 := hrate 1
    have hCD : C + D = 1 := by
      rw [← hpoly01, hrate1]
    rw [hD] at hCD
    simpa using hCD
  have hA : A = -1 := by
    have hpoly11 : f 1 1 = A + B + C + D := by
      have h := hpoly 1 1
      ring_nf at h ⊢
      exact h
    have habs1 : f 1 1 = 1 := habs 1
    have hABCD : A + B + C + D = 1 := by
      rw [← hpoly11, habs1]
    rw [hB, hC, hD] at hABCD
    nlinarith
  intro h σ
  rw [hpoly h σ, hA, hB, hC, hD]
  unfold bumpSatField
  ring

/-- THEOREM 3: the same biaffine endpoint laws force the complement residual
law itself. -/
theorem complement_residual_law_of_biaffine_endpoint_laws
    (f : ℝ -> ℝ -> ℝ)
    (hlin : IsBiaffineUpdate f)
    (hid : ∀ h : ℝ, f h 0 = h)
    (hrate : ∀ σ : ℝ, f 0 σ = σ)
    (habs : ∀ σ : ℝ, f 1 σ = 1) :
    ∀ h σ : ℝ, 1 - f h σ = (1 - h) * (1 - σ) := by
  intro h σ
  rw [bumpSat_unique_of_biaffine_endpoint_laws f hlin hid hrate habs]
  unfold bumpSatField
  ring

/-! ## Convex closure is the forced interval behavior -/

/-- THEOREM 4: the unique update forced by the endpoint/complement laws is
closed on the unit interval. -/
theorem bumpSat_unique_convex_interval_closure
    (h σ : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 ≤ bumpSatField h σ ∧ bumpSatField h σ ≤ 1 :=
  bumpSatField_mem_Icc h σ hh0 hh1 hσ0 hσ1

/-! ## Certificate -/

/-- P717 certificate: complement residual accounting plus biaffine endpoint
laws make `bumpSatField` the unique target-one update, and the forced update is
closed on `[0,1]`. -/
structure BumpSatUniquenessCertificate : Prop where
  complement_residual_unique :
    ∀ f : ℝ -> ℝ -> ℝ,
      (∀ h σ : ℝ, 1 - f h σ = (1 - h) * (1 - σ)) ->
      ∀ h σ : ℝ, f h σ = bumpSatField h σ
  biaffine_endpoint_unique :
    ∀ f : ℝ -> ℝ -> ℝ,
      IsBiaffineUpdate f ->
      (∀ h : ℝ, f h 0 = h) ->
      (∀ σ : ℝ, f 0 σ = σ) ->
      (∀ σ : ℝ, f 1 σ = 1) ->
      ∀ h σ : ℝ, f h σ = bumpSatField h σ
  biaffine_endpoint_residual_law :
    ∀ f : ℝ -> ℝ -> ℝ,
      IsBiaffineUpdate f ->
      (∀ h : ℝ, f h 0 = h) ->
      (∀ σ : ℝ, f 0 σ = σ) ->
      (∀ σ : ℝ, f 1 σ = 1) ->
      ∀ h σ : ℝ, 1 - f h σ = (1 - h) * (1 - σ)
  convex_interval_closure :
    ∀ h σ : ℝ,
      0 ≤ h -> h ≤ 1 -> 0 ≤ σ -> σ ≤ 1 ->
      0 ≤ bumpSatField h σ ∧ bumpSatField h σ ≤ 1

/-- THEOREM 5: the real scalar carrier supplies the P717 uniqueness
certificate. -/
theorem bumpSatUniquenessCertificate :
    BumpSatUniquenessCertificate where
  complement_residual_unique := bumpSat_unique_of_complement_residual_law
  biaffine_endpoint_unique := bumpSat_unique_of_biaffine_endpoint_laws
  biaffine_endpoint_residual_law :=
    complement_residual_law_of_biaffine_endpoint_laws
  convex_interval_closure := bumpSat_unique_convex_interval_closure

end AffineRelaxation
end SaturationMonoid
