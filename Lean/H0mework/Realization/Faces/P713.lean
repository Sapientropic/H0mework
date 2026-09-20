import H0mework.Realization.Fibres.P314

/-!
# Proposition 713: the seven-symbol ontology spine

The previous central chain (P710-P712) closes the finite three-nail readout:
readout, no-family freedom, and the canonical proof principle.  This file
extracts the lower algebraic spine named in the notes:

`X -> X + sigma * (T - X)`.

In Lean the carrier-general form is

`relaxModule target sigma x = x + sigma • (target - x)`.

From that one affine relaxation shape, together with the already-proved
iteration/complement/carrier theorems, this file packages the ten basic
structures:

* geometric residual decay;
* target/current direction symmetry of the residual law;
* complement duality;
* finite time folding, `n` steps as one step;
* `satOr` composition;
* absorbing endpoint;
* identity/no-op start;
* sigma exponent carrier equivalent to `Nat`;
* rate/keep duality;
* the active interval `0 < sigma < 1` and `[0,1]` closure.

Boundary: this is the algebraic ontology spine.  It does not derive smooth
Standard-Model threshold dynamics, universal QFT loop weights, arbitrary
Hamiltonians, Goldbach/RH, polynomial SAT, `P = NP`, or empirical physics.
-/

noncomputable section

set_option linter.checkUnivs false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u v

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type v} [AddCommGroup E] [Module K E]

/-- P713 certificate: the ten named structures forced by the affine
relaxation equation on an active sigma carrier. -/
structure SevenSymbolOntologySpineCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  seven_symbol_formula :
    ∀ target x : E,
      relaxModule target σ x = x + σ • (target - x)
  geometric_decay :
    ∀ target x : E, ∀ n : ℕ,
      target - (fun y : E => relaxModule target σ y)^[n] x =
        ((1 - σ) ^ n) • (target - x)
  direction_symmetric_residual :
    ∀ x target : E,
      (target - relaxModule target σ x = (1 - σ) • (target - x)) ∧
        (x - relaxModule x σ target = (1 - σ) • (x - target))
  complement_invariant :
    ∀ a b : K,
      complement (satOrField a b) = complement a * complement b
  time_folding :
    ∀ target x : E, ∀ n : ℕ,
      (fun y : E => relaxModule target σ y)^[n] x =
        relaxModule target (iteratedRate σ n) x
  satOr_composition :
    ∀ target x : E, ∀ σ₁ σ₂ : K,
      relaxModule target σ₂ (relaxModule target σ₁ x) =
        relaxModule target (satOrField σ₁ σ₂) x
  absorbing_endpoint :
    ∀ target : E,
      relaxModule target σ target = target
  identity_start :
    ∀ target x : E,
      relaxModule target (0 : K) x = x
  carrier_equiv_nat :
    SigmaExponentImage σ ≃ ℕ
  carrier_add_reflects_nat :
    ∀ n m k : ℕ,
      SigmaExponentImage.add (SigmaExponentImage.ofNat σ n)
          (SigmaExponentImage.ofNat σ m) =
        SigmaExponentImage.ofNat σ k ↔
      n + m = k
  rate_keep_duality :
    ∀ h ρ : K,
      complement (bumpSatField h ρ) = complement h * complement ρ
  active_interval :
    0 < σ ∧ σ < 1
  active_interval_closed :
    (∀ σ₁ σ₂ : K,
      0 ≤ σ₁ -> σ₁ ≤ 1 -> 0 ≤ σ₂ -> σ₂ ≤ 1 ->
        0 ≤ satOrField σ₁ σ₂ ∧ satOrField σ₁ σ₂ ≤ 1) ∧
    (∀ h ρ : K,
      0 ≤ h -> h ≤ 1 -> 0 ≤ ρ -> ρ ≤ 1 ->
        0 ≤ bumpSatField h ρ ∧ bumpSatField h ρ ≤ 1)

/-- THEOREM 1: the affine relaxation equation supplies the full seven-symbol
ontology spine on every active sigma carrier. -/
def sevenSymbolOntologySpineCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SevenSymbolOntologySpineCertificate (K := K) (E := E) σ hσ0 hσ1 where
  seven_symbol_formula := by
    intro target x
    rfl
  geometric_decay := by
    intro target x n
    exact target_sub_relaxModule_iterate target σ x n
  direction_symmetric_residual := by
    intro x target
    exact ⟨target_sub_relaxModule target σ x,
      target_sub_relaxModule x σ target⟩
  complement_invariant := by
    intro a b
    exact complement_satOrField a b
  time_folding := by
    intro target x n
    exact relaxModule_iterate_eq_single_iteratedRate target σ x n
  satOr_composition := by
    intro target x σ₁ σ₂
    exact relaxModule_compose target x σ₁ σ₂
  absorbing_endpoint := by
    intro target
    exact relaxModule_target_absorbing target σ
  identity_start := by
    intro target x
    exact relaxModule_zero target x
  carrier_equiv_nat :=
    SigmaExponentImage.equivNatOfMemIoo hσ0 hσ1
  carrier_add_reflects_nat := by
    intro n m k
    exact SigmaExponentImage.add_eq_ofNat_iff_add_eq_of_mem_Ioo
      hσ0 hσ1
  rate_keep_duality := by
    intro h ρ
    exact complement_bumpSatField h ρ
  active_interval := ⟨hσ0, hσ1⟩
  active_interval_closed := by
    exact ⟨satOrField_mem_Icc, bumpSatField_mem_Icc⟩

end AffineRelaxation
end SaturationMonoid
