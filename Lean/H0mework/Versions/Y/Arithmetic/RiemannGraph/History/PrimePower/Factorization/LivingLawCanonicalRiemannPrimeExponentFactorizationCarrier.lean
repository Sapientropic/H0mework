import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.LivingLawCanonicalRiemannConductorPrimePowerRoot

/-!
# Prime-exponent multiplicative factorization carrier

The receipt current is additive in individual `(p,k)` rows.  Multiplicative
composition requires the full finitely supported exponent lattice.  Its
additive monoid algebra is the canonical integral carrier of products and
inverse products of prime scales.  The realization into the existing
positive-scale group ring sends each exponent vector to its actual scale.

Every receipt boundary factors through this carrier before reaching
`IntegralScaleCarrier`; exponent forgetting is therefore a downstream
compression, not the parent representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History
namespace PrimePowerCurrent

open ActionCofiber.RawEffect
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimePower.Source
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

/-- Finite integral valuations at all rational primes. -/
abbrev PrimeExponentLattice := Nat.Primes →₀ ℤ

/-- One prime sends an integer exponent to the corresponding positive scale.
The additive target is the multiplicative group of positive units. -/
def primeExponentScaleGenerator (prime : Nat.Primes) :
    ℤ →+ Additive (Units NNReal) where
  toFun exponent := Additive.ofMul ((blockPrimeScaleUnit prime) ^ exponent)
  map_zero' := by simp
  map_add' left right := by
    change (blockPrimeScaleUnit prime) ^ (left + right) =
      (blockPrimeScaleUnit prime) ^ left *
        (blockPrimeScaleUnit prime) ^ right
    exact zpow_add (blockPrimeScaleUnit prime) left right

def primeExponentScaleAddHom :
    PrimeExponentLattice →+ Additive (Units NNReal) :=
  Finsupp.liftAddHom fun prime => primeExponentScaleGenerator prime

/-- Actual positive scale represented by one finite valuation vector. -/
def primeExponentScale (value : PrimeExponentLattice) : Units NNReal :=
  Additive.toMul (primeExponentScaleAddHom value)

@[simp] theorem primeExponentScale_single
    (prime : Nat.Primes) (exponent : ℤ) :
    primeExponentScale (Finsupp.single prime exponent) =
      (blockPrimeScaleUnit prime) ^ exponent := by
  simp [primeExponentScale, primeExponentScaleAddHom,
    primeExponentScaleGenerator]

@[simp] theorem primeExponentScale_zero :
    primeExponentScale 0 = 1 := by
  simp [primeExponentScale]

@[simp] theorem primeExponentScale_add
    (left right : PrimeExponentLattice) :
    primeExponentScale (left + right) =
      primeExponentScale left * primeExponentScale right := by
  simp [primeExponentScale]

def primeExponentScaleMonoidHom :
    Multiplicative PrimeExponentLattice →* Units NNReal where
  toFun value := primeExponentScale (Multiplicative.toAdd value)
  map_one' := primeExponentScale_zero
  map_mul' left right := by
    exact primeExponentScale_add (Multiplicative.toAdd left)
      (Multiplicative.toAdd right)

/-- Integral group ring of the complete finite prime-valuation lattice. -/
abbrev PrimeExponentFactorizationCarrier :=
  AddMonoidAlgebra ℤ PrimeExponentLattice

def primeExponentBasisToIntegral :
    Multiplicative PrimeExponentLattice →* IntegralScaleCarrier :=
  (MonoidAlgebra.of ℤ (Units NNReal)).comp primeExponentScaleMonoidHom

/-- Canonical multiplicative realization into the existing positive-scale
group ring. -/
def primeExponentIntegralRealization :
    PrimeExponentFactorizationCarrier →ₐ[ℤ] IntegralScaleCarrier :=
  AddMonoidAlgebra.lift ℤ IntegralScaleCarrier PrimeExponentLattice
    primeExponentBasisToIntegral

@[simp] theorem primeExponentIntegralRealization_single
    (value : PrimeExponentLattice) (coefficient : ℤ) :
    primeExponentIntegralRealization
        (AddMonoidAlgebra.single value coefficient) =
      coefficient • delta (primeExponentScale value) := by
  simp [primeExponentIntegralRealization, primeExponentBasisToIntegral,
    primeExponentScaleMonoidHom, delta]

def primePowerExponentVector (index : ConductorPrimePowerIndex) :
    PrimeExponentLattice :=
  Finsupp.single index.1 (index.2.1 : ℤ)

theorem primeExponentScale_primePower
    (index : ConductorPrimePowerIndex) :
    primeExponentScale (primePowerExponentVector index) =
      primePowerUnit index.1 index.2.1 := by
  rw [primePowerExponentVector, primeExponentScale_single]
  apply Units.ext
  apply NNReal.eq
  simp [primePowerUnit,
    ClozelGeneralizedDual.thetaDistributionPrimePower,
    blockPrimeScaleUnit, positiveRealUnit_val]

/-- Receipt boundary before any Archimedean or detector read. -/
def factorizationBoundaryValue (index : ConductorPrimePowerIndex) :
    PrimeExponentFactorizationCarrier :=
  AddMonoidAlgebra.single 0 1 -
    AddMonoidAlgebra.single (primePowerExponentVector index) 1

def factorizationBoundaryMap :
    ConductorPrimePowerCurrent →ₗ[ℤ]
      PrimeExponentFactorizationCarrier :=
  (Finsupp.liftAddHom fun index =>
    AddMonoidHom.flip
      (smulAddHom ℤ PrimeExponentFactorizationCarrier)
      (factorizationBoundaryValue index)).toIntLinearMap

@[simp] theorem factorizationBoundaryMap_single
    (index : ConductorPrimePowerIndex) (coefficient : ℤ) :
    factorizationBoundaryMap (Finsupp.single index coefficient) =
      coefficient • factorizationBoundaryValue index := by
  simp [factorizationBoundaryMap]

theorem primeExponentIntegralRealization_boundaryValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    primeExponentIntegralRealization (factorizationBoundaryValue index) =
      integralBoundaryValue observation nontrivial index := by
  rw [factorizationBoundaryValue, map_sub,
    primeExponentIntegralRealization_single,
    primeExponentIntegralRealization_single]
  simp only [one_smul, primeExponentScale_zero,
    primeExponentScale_primePower]
  exact (primePowerBoundaryIntegralRead_eq observation nontrivial
    index.1 index.2.1 index.2.2).symm

/-- The whole receipt inventory first lands in the multiplicative
factorization carrier, then literally recovers the installed integral map. -/
theorem factorization_integral_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    primeExponentIntegralRealization.toLinearMap.comp
        factorizationBoundaryMap =
      integralBoundaryMap observation nontrivial := by
  apply LinearMap.ext
  intro current
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      simp only [map_add, leftHypothesis, rightHypothesis]
  | single index coefficient =>
      change primeExponentIntegralRealization
          (factorizationBoundaryMap
            (Finsupp.single index coefficient)) =
        integralBoundaryMap observation nontrivial
          (Finsupp.single index coefficient)
      rw [factorizationBoundaryMap_single,
        integralBoundaryMap_single, map_smul]
      exact congrArg (fun value : IntegralScaleCarrier => coefficient • value)
        (primeExponentIntegralRealization_boundaryValue
          observation nontrivial index)

/-- The coordinate erased by the old all-prime face remains nonzero after
the new factorization carrier reaches the actual integral boundary. -/
theorem factorizationBoundaryMap_exponentCompressionResidual_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    factorizationBoundaryMap (exponentCompressionResidual prime) ≠ 0 := by
  intro factorizationZero
  have integralZero := congrArg primeExponentIntegralRealization
    factorizationZero
  rw [map_zero] at integralZero
  have integralLinearZero :
      primeExponentIntegralRealization.toLinearMap
          (factorizationBoundaryMap
            (exponentCompressionResidual prime)) = 0 :=
    integralZero
  have square := LinearMap.congr_fun
    (factorization_integral_square observation nontrivial)
    (exponentCompressionResidual prime)
  rw [LinearMap.comp_apply, integralLinearZero] at square
  exact integralBoundaryMap_exponentCompressionResidual_ne_zero
    observation nontrivial prime square.symm

end
end PrimePowerCurrent
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
