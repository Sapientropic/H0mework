import Mathlib.NumberTheory.Padics.PadicVal.Basic
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentFactorizationCarrier

/-!
# Faithfulness of the prime-exponent realization

The rational scale of a finite integral prime-valuation vector remembers
every coordinate: the `p`-adic valuation recovers the exponent at `p`.
Casting this scale to the positive-real unit proves that the Archimedean
scale map is injective.  Consequently the induced integral group-ring
realization is faithful; no unique-factorization or nondegeneracy premise is
supplied by a caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent

noncomputable section

def primeExponentRationalScale (value : PrimeExponentLattice) : ℚ :=
  value.prod fun prime exponent => ((prime : Nat) : ℚ) ^ exponent

@[simp] theorem primeExponentRationalScale_single
    (prime : Nat.Primes) (exponent : ℤ) :
    primeExponentRationalScale (Finsupp.single prime exponent) =
      ((prime : Nat) : ℚ) ^ exponent := by
  simp [primeExponentRationalScale]

@[simp] theorem primeExponentRationalScale_add
    (left right : PrimeExponentLattice) :
    primeExponentRationalScale (left + right) =
      primeExponentRationalScale left * primeExponentRationalScale right := by
  rw [primeExponentRationalScale, Finsupp.prod_add_index]
  · rfl
  · intro prime _
    simp
  · intro prime _ leftExponent rightExponent
    have prime_ne : (((prime : Nat) : ℚ) ≠ 0) := by
      exact_mod_cast prime.property.ne_zero
    exact zpow_add₀ prime_ne leftExponent rightExponent

theorem primeExponentRationalScale_ne_zero
    (value : PrimeExponentLattice) :
    primeExponentRationalScale value ≠ 0 := by
  classical
  induction value using Finsupp.induction with
  | zero => simp [primeExponentRationalScale]
  | single_add prime exponent value _prime_not_mem _exponent_ne ih =>
      rw [primeExponentRationalScale_add,
        primeExponentRationalScale_single]
      have prime_ne : (((prime : Nat) : ℚ) ≠ 0) := by
        exact_mod_cast prime.property.ne_zero
      exact mul_ne_zero (zpow_ne_zero _ prime_ne) ih

/-- Each rational prime valuation reads exactly one lattice coordinate. -/
theorem padicValRat_primeExponentRationalScale
    (value : PrimeExponentLattice) (prime : Nat.Primes) :
    padicValRat (prime : Nat) (primeExponentRationalScale value) =
      value prime := by
  classical
  let _ : Fact (Nat.Prime (prime : Nat)) := ⟨prime.property⟩
  induction value using Finsupp.induction with
  | zero => simp [primeExponentRationalScale, padicValRat.one]
  | single_add other exponent value _other_not_mem exponent_ne ih =>
      rw [primeExponentRationalScale_add,
        primeExponentRationalScale_single]
      have other_ne : (((other : Nat) : ℚ) ≠ 0) := by
        exact_mod_cast other.property.ne_zero
      rw [padicValRat.mul (zpow_ne_zero _ other_ne)
        (primeExponentRationalScale_ne_zero value),
        padicValRat.zpow, ih, Finsupp.add_apply]
      by_cases other_eq : other = prime
      · subst other
        rw [padicValRat.self prime.property.one_lt]
        simp
      · let _ : Fact (Nat.Prime (other : Nat)) := ⟨other.property⟩
        rw [padicValRat.of_nat, padicValNat_primes]
        · simp [other_eq]
        · exact Subtype.coe_ne_coe.mpr (Ne.symm other_eq)

theorem primeExponentRationalScale_injective :
    Function.Injective primeExponentRationalScale := by
  intro left right equality
  ext prime
  rw [← padicValRat_primeExponentRationalScale left prime,
    ← padicValRat_primeExponentRationalScale right prime, equality]

/-- Rational and positive-real scale faces are the same source coordinate. -/
theorem primeExponentRationalScale_cast_real
    (value : PrimeExponentLattice) :
    (primeExponentRationalScale value : ℝ) =
      ClozelGeneralizedDual.ThetaJRoleRepresentation.scaleValue
        (primeExponentScale value) := by
  classical
  induction value using Finsupp.induction with
  | zero =>
      simp [primeExponentRationalScale,
        ClozelGeneralizedDual.ThetaJRoleRepresentation.scaleValue]
  | single_add prime exponent value _prime_not_mem _exponent_ne ih =>
      rw [primeExponentRationalScale_add, primeExponentScale_add,
        Rat.cast_mul, ih,
        ClozelGeneralizedDual.ThetaJRoleRepresentation.scaleValue_mul,
        primeExponentRationalScale_single, primeExponentScale_single]
      congr 1
      simp [ActionCofiber.RawEffect.blockPrimeScaleUnit,
        ClozelGeneralizedDual.ThetaJRoleRepresentation.scaleValue,
        SourceGeneratedPositiveRealCharacter.positiveRealUnit_val]

theorem primeExponentScale_injective :
    Function.Injective primeExponentScale := by
  intro left right equality
  apply primeExponentRationalScale_injective
  have castEquality : (primeExponentRationalScale left : ℝ) =
      (primeExponentRationalScale right : ℝ) := by
    rw [primeExponentRationalScale_cast_real,
      primeExponentRationalScale_cast_real, equality]
  exact_mod_cast castEquality

theorem primeExponentIntegralRealization_coefficients
    (value : PrimeExponentFactorizationCarrier) :
    MonoidAlgebra.coeffLinearEquiv ℤ
        (primeExponentIntegralRealization value) =
      (AddMonoidAlgebra.coeffLinearEquiv ℤ value).mapDomain
        primeExponentScale := by
  let coefficients := AddMonoidAlgebra.coeffLinearEquiv ℤ value
  have value_eq : value =
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm coefficients := by
    exact (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm_apply_apply value |>.symm
  rw [value_eq]
  change MonoidAlgebra.coeffLinearEquiv ℤ
      (primeExponentIntegralRealization
        ((AddMonoidAlgebra.coeffLinearEquiv ℤ).symm coefficients)) =
    coefficients.mapDomain primeExponentScale
  induction coefficients using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      simp only [map_add]
      rw [leftHypothesis, rightHypothesis]
      exact ((Finsupp.mapDomain.addMonoidHom primeExponentScale
        ).map_add left right).symm
  | single exponent coefficient =>
      ext scale
      by_cases scale_eq : primeExponentScale exponent = scale
      · subst scale
        simp [primeExponentIntegralRealization_single,
          SourceGeneratedIntegralCharacterGroupRing.delta]
      · simp [primeExponentIntegralRealization_single,
          SourceGeneratedIntegralCharacterGroupRing.delta, scale_eq]

theorem primeExponentIntegralRealization_injective :
    Function.Injective primeExponentIntegralRealization := by
  intro left right equality
  apply (AddMonoidAlgebra.coeffLinearEquiv ℤ).injective
  apply Finsupp.mapDomain_injective primeExponentScale_injective
  rw [← primeExponentIntegralRealization_coefficients,
    ← primeExponentIntegralRealization_coefficients, equality]

end
end MuntzGraph.Conductor.History.PrimePowerCurrent
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
