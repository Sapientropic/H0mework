import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Inventory

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

variable {L : Type u} [AddCommGroup L]

theorem modulus_source_fibre (modulus : Nat) (positive : modulus ≠ 0) (left right : L) :
    modulusProjection modulus left = modulusProjection modulus right ↔
      ∃ difference : L, (modulus : ℤ) • difference = left - right := by
  let read := modulusEquiv (L := L) modulus positive
  have readEqual : modulusProjection modulus left = modulusProjection modulus right ↔
      finitePrimeProjection (modulusPrimes modulus) (modulusDepth modulus) left =
        finitePrimeProjection (modulusPrimes modulus) (modulusDepth modulus) right := by
    rw [← modulus_equiv_projection modulus positive, ← modulus_equiv_projection modulus positive]
    exact read.injective.eq_iff.symm
  rw [readEqual, finite_prime_fibre, composite_modulus_factorization positive]

private def factorialStageLift (value : FactorialCompletion (L := L)) (stage : Nat) : L :=
  Classical.choose ((modulusRange (L := L) (factorialModulus stage)).mkQ_surjective
    ((factorialRestriction (L := L) stage).hom value))

private theorem factorial_stage_lift_read (value : FactorialCompletion (L := L)) (stage : Nat) :
    modulusProjection (factorialModulus stage) (factorialStageLift value stage) =
      (factorialRestriction (L := L) stage).hom value :=
  Classical.choose_spec ((modulusRange (L := L) (factorialModulus stage)).mkQ_surjective
    ((factorialRestriction (L := L) stage).hom value))

/-- Pick the unique signed representative in the original half-open modulus interval. -/
def factorialBalancedLift (coordinate : L ≃ₗ[ℤ] ℤ)
    (value : FactorialCompletion (L := L)) (stage : Nat) : L :=
  let modulus := (factorialModulus stage : ℤ)
  let integer := coordinate (factorialStageLift value stage)
  coordinate.symm ((integer + modulus/2) % modulus - modulus/2)

theorem factorial_balanced_lift (coordinate : L ≃ₗ[ℤ] ℤ)
    (value : FactorialCompletion (L := L)) (stage : Nat) :
    let modulus := (factorialModulus stage : ℤ)
    let source := factorialBalancedLift coordinate value stage
    modulusProjection (factorialModulus stage) source = (factorialRestriction (L := L) stage).hom value ∧
      -(modulus/2) ≤ coordinate source ∧ coordinate source < modulus - modulus/2 := by
  dsimp only
  let modulus := (factorialModulus stage : ℤ)
  let lifted := factorialStageLift value stage
  let integer := coordinate lifted
  let source := factorialBalancedLift coordinate value stage
  have coefficient : coordinate source = (integer + modulus/2) % modulus - modulus/2 :=
    coordinate.apply_symm_apply _
  have positive : 0 < modulus := by
    change (0 : ℤ) < (factorialModulus stage : ℤ)
    exact_mod_cast Nat.pos_of_ne_zero (factorial_modulus_ne_zero stage)
  have congruent : modulusProjection (factorialModulus stage) source =
      modulusProjection (factorialModulus stage) lifted := by
    apply (modulus_source_fibre (factorialModulus stage) (factorial_modulus_ne_zero stage) source lifted).2
    refine ⟨coordinate.symm (-((integer + modulus/2)/modulus)), coordinate.injective ?_⟩
    rw [map_smul, map_sub, coefficient, coordinate.apply_symm_apply]
    change modulus * -((integer + modulus/2)/modulus) =
      ((integer + modulus/2) % modulus - modulus/2) - integer
    have divided := Int.emod_add_ediv_mul (integer + modulus/2) modulus
    rw [mul_comm ((integer + modulus/2)/modulus) modulus] at divided
    rw [mul_neg]
    omega
  have lower := Int.emod_nonneg (integer + modulus/2) positive.ne'
  have upper := Int.emod_lt_of_pos (integer + modulus/2) positive
  change _ ∧ -(modulus/2) ≤ coordinate source ∧ coordinate source < modulus - modulus/2
  rw [coefficient]
  exact ⟨congruent.trans (factorial_stage_lift_read value stage), by omega, by omega⟩

theorem factorial_balanced_unique (coordinate : L ≃ₗ[ℤ] ℤ) (stage : Nat) {left right : L}
    (leftBounds : -((factorialModulus stage : ℤ)/2) ≤ coordinate left ∧
      coordinate left < (factorialModulus stage : ℤ) - (factorialModulus stage : ℤ)/2)
    (rightBounds : -((factorialModulus stage : ℤ)/2) ≤ coordinate right ∧
      coordinate right < (factorialModulus stage : ℤ) - (factorialModulus stage : ℤ)/2)
    (same : modulusProjection (factorialModulus stage) left = modulusProjection (factorialModulus stage) right) :
    left = right := by
  obtain ⟨difference, divided⟩ :=
    (modulus_source_fibre (factorialModulus stage) (factorial_modulus_ne_zero stage) left right).1 same
  let modulus := (factorialModulus stage : ℤ)
  have positive : 0 < modulus := by
    change (0 : ℤ) < (factorialModulus stage : ℤ)
    exact_mod_cast Nat.pos_of_ne_zero (factorial_modulus_ne_zero stage)
  have written := congrArg coordinate divided
  rw [map_smul, map_sub, smul_eq_mul] at written
  have multiple : modulus ∣ coordinate left - coordinate right := ⟨coordinate difference, written.symm⟩
  have small : (coordinate left - coordinate right).natAbs < modulus.natAbs := by
    change _ < (factorialModulus stage : ℤ).natAbs
    dsimp only [modulus] at positive
    omega
  exact coordinate.injective (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs multiple small))

/-- On the diagonal, the signed representatives eventually coincide with the original source. -/
theorem factorial_balanced_diagonal (coordinate : L ≃ₗ[ℤ] ℤ) (source : L) :
    ∃ base : Nat, ∀ stage ≥ base, factorialBalancedLift coordinate (factorialCanonicalMap source) stage = source := by
  refine ⟨2*(coordinate source).natAbs+2, fun stage late => ?_⟩
  let modulus := (factorialModulus stage : ℤ)
  have large : 2*(coordinate source).natAbs+2 ≤ factorialModulus stage :=
    late.trans ((Nat.le_succ stage).trans (Nat.self_le_factorial (stage+1)))
  have actual := factorial_balanced_lift coordinate (factorialCanonicalMap source) stage
  dsimp only at actual
  have bounds : -(modulus/2) ≤ coordinate source ∧ coordinate source < modulus - modulus/2 := by
    dsimp only [modulus]
    omega
  exact factorial_balanced_unique coordinate stage actual.2 bounds
    (actual.1.trans (factorial_canonical_restriction stage source))

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
