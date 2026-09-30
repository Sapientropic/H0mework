import H0mework.Arithmetic.EulerDerived.EndpointZeroFiberState
import H0mework.Arithmetic.RiemannSource.NontrivialCompletedZero

/-!
# Finite Euler nonvanishing at a generated Riemann zero

Every installed finite Euler factor is nonzero at an owner-indexed generated
zeta zero, on both the selected and reversal coordinates.  Consequently no
coefficient-preserving point of any existing finite formal block zero fibre
can realize that analytic zero.

This is the exact finite/infinite cutoff needed by Tate--Meyer style attacks:
the zero may live in an infinite topological cokernel, but it is not already a
root of one of the repository's finite Euler determinant sections.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryZeroFiberCokernelGlobalState

noncomputable section

namespace GeneratedRiemannZeroObservationAt

theorem coordinate_ne_one {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    observation.coordinate ≠ 1 := by
  intro coordinateOne
  apply riemannZeta_ne_zero_of_one_le_re (s := observation.coordinate)
    (by rw [coordinateOne]; norm_num)
  exact observation.mathlibZero

/-- A generated zeta zero cannot lie on the imaginary axis. -/
theorem coordinate_realPart_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    observation.coordinate.re ≠ 0 := by
  intro realZero
  have avoidsNegativeNaturals :
      ∀ n : ℕ, observation.coordinate ≠ -(n : ℂ) := by
    intro n equality
    have realEquality := congrArg Complex.re equality
    change observation.coordinate.re = -(n : ℝ) at realEquality
    rw [realZero] at realEquality
    have nCastZero : (n : ℝ) = 0 := by linarith
    have nZero : n = 0 := by exact_mod_cast nCastZero
    subst n
    simp only [Nat.cast_zero, neg_zero] at equality
    exact observation.coordinate_ne_zero equality
  have functional := riemannZeta_one_sub
    avoidsNegativeNaturals observation.coordinate_ne_one
  rw [observation.mathlibZero, mul_zero] at functional
  have reflectedNonzero : riemannZeta (1 - observation.coordinate) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by
      change 1 ≤ 1 - observation.coordinate.re
      rw [realZero]
      norm_num)
  exact reflectedNonzero functional

theorem coordinate_realPart_ne_one {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    observation.coordinate.re ≠ 1 := by
  intro realOne
  exact (riemannZeta_ne_zero_of_one_le_re (by linarith))
    observation.mathlibZero

theorem reversal_realPart_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    (coordinateReversal observation.coordinate).re ≠ 0 := by
  intro reversalZero
  apply observation.coordinate_realPart_ne_one
  change 1 - observation.coordinate.re = 0 at reversalZero
  linarith

theorem installedPrimeEigenvalue_ne_one_of_realPart_ne_zero
    (prime : Nat.Primes) (coordinate : ℂ)
    (realPart : coordinate.re ≠ 0) :
    installedPrimeEigenvalue prime coordinate ≠ 1 := by
  intro equality
  have normEquality := congrArg norm equality
  rw [installedPrimeEigenvalue,
    Complex.norm_natCast_cpow_of_re_ne_zero prime (by
      simpa using realPart)] at normEquality
  simp only [norm_one] at normEquality
  have exponentEquality : -coordinate.re = 0 := by
    apply (Real.rpow_right_inj
      (x := (prime : ℝ)) (y := -coordinate.re) (z := 0)
      (by exact_mod_cast prime.property.pos)
      (by exact_mod_cast prime.property.ne_one)).mp
    simpa using normEquality
  exact realPart (by linarith)

/-- Both local factors belonging to the selected/reversal pair are nonzero. -/
theorem finiteEulerPairFactor_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (prime : Nat.Primes) :
    (1 - installedPrimeEigenvalue prime observation.coordinate) ≠ 0 ∧
      (1 - installedPrimeEigenvalue prime
        (coordinateReversal observation.coordinate)) ≠ 0 := by
  constructor <;> rw [sub_ne_zero]
  · exact (installedPrimeEigenvalue_ne_one_of_realPart_ne_zero
      prime observation.coordinate observation.coordinate_realPart_ne_zero).symm
  · exact (installedPrimeEigenvalue_ne_one_of_realPart_ne_zero
      prime (coordinateReversal observation.coordinate)
      observation.reversal_realPart_ne_zero).symm

/-- Every actual finite block determinant is nonzero at a generated zeta zero
and its canonical reversal. -/
theorem finiteBlockDeterminant_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) :
    installedBlockEvaluation
        (blockDeterminantSection seedOccurrence.root stage)
        (observation.coordinate,
          coordinateReversal observation.coordinate) ≠ 0 := by
  rw [installedBlockEvaluation_section]
  apply Finset.prod_ne_zero_iff.mpr
  intro primeIndex _membership
  apply mul_ne_zero
  · exact (observation.finiteEulerPairFactor_ne_zero
      ((stageFactorization seedOccurrence.root stage).actualPrime
        primeIndex)).1
  · exact (observation.finiteEulerPairFactor_ne_zero
      ((stageFactorization seedOccurrence.root stage).actualPrime
        primeIndex)).2

/-! ## Finite algebraic kernel and cokernel deletion -/

def finiteBlockScalarEndomorphism {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) (Carrier : Type*)
    [AddCommGroup Carrier] [Module ℂ Carrier] :
    Carrier →ₗ[ℂ] Carrier :=
  installedBlockEvaluation
      (blockDeterminantSection seedOccurrence.root stage)
      (observation.coordinate,
        coordinateReversal observation.coordinate) • LinearMap.id

@[simp] theorem finiteBlockScalarEndomorphism_apply
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) {Carrier : Type*}
    [AddCommGroup Carrier] [Module ℂ Carrier]
    (value : Carrier) :
    observation.finiteBlockScalarEndomorphism stage Carrier value =
      installedBlockEvaluation
          (blockDeterminantSection seedOccurrence.root stage)
          (observation.coordinate,
            coordinateReversal observation.coordinate) • value :=
  rfl

theorem finiteBlockScalarEndomorphism_ker_eq_bot
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) (Carrier : Type*)
    [AddCommGroup Carrier] [Module ℂ Carrier] :
    (observation.finiteBlockScalarEndomorphism stage Carrier).ker = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro left right equality
  have scalarNe := observation.finiteBlockDeterminant_ne_zero stage
  have differenceZero :
      installedBlockEvaluation
          (blockDeterminantSection seedOccurrence.root stage)
          (observation.coordinate,
            coordinateReversal observation.coordinate) •
        (left - right) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr equality
  have : left - right = 0 :=
    (smul_eq_zero.mp differenceZero).resolve_left scalarNe
  exact sub_eq_zero.mp this

theorem finiteBlockScalarEndomorphism_range_eq_top
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) (Carrier : Type*)
    [AddCommGroup Carrier] [Module ℂ Carrier] :
    (observation.finiteBlockScalarEndomorphism stage Carrier).range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro target
  let scalar :=
    installedBlockEvaluation
      (blockDeterminantSection seedOccurrence.root stage)
      (observation.coordinate,
        coordinateReversal observation.coordinate)
  have scalarNe : scalar ≠ 0 := observation.finiteBlockDeterminant_ne_zero stage
  refine ⟨scalar⁻¹ • target, ?_⟩
  change scalar • (scalar⁻¹ • target) = target
  rw [← mul_smul, mul_inv_cancel₀ scalarNe, one_smul]

abbrev FiniteBlockAlgebraicCokernel {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) (Carrier : Type*)
    [AddCommGroup Carrier] [Module ℂ Carrier] :=
  Carrier ⧸
    (observation.finiteBlockScalarEndomorphism stage Carrier).range

theorem finiteBlockAlgebraicCokernel_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) (Carrier : Type*)
    [AddCommGroup Carrier] [Module ℂ Carrier]
    (value : observation.FiniteBlockAlgebraicCokernel stage Carrier) :
    value = 0 := by
  obtain ⟨representative, rfl⟩ :=
    (observation.finiteBlockScalarEndomorphism stage Carrier).range.mkQ_surjective
      value
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    observation.finiteBlockScalarEndomorphism_range_eq_top stage Carrier]
  trivial

/-- Any finite-stage map required to land in the actual finite Euler kernel
is the zero map. -/
theorem map_into_finiteBlockKernel_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) {Source Carrier : Type*}
    [AddCommGroup Source] [Module ℂ Source]
    [AddCommGroup Carrier] [Module ℂ Carrier]
    (map : Source →ₗ[ℂ] Carrier)
    (landsInKernel : map.range ≤
      (observation.finiteBlockScalarEndomorphism stage Carrier).ker) :
    map = 0 := by
  rw [observation.finiteBlockScalarEndomorphism_ker_eq_bot
    stage Carrier] at landsInKernel
  exact LinearMap.range_eq_bot.mp (le_bot_iff.mp landsInKernel)

/-- A point of the actual local formal block zero fibre which would extend
the installed selected/reversal evaluation. -/
structure LocalBlockZeroFiberSpecialization {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) where
  map : LocalGeneratedBlockZeroFiberRing stage →+* ℂ
  extendsEvaluation : ∀ coefficient : BlockCoordinateRing,
    map (algebraMap BlockCoordinateRing
      (LocalGeneratedBlockZeroFiberRing stage) coefficient) =
        installedBlockEvaluation coefficient
          (observation.coordinate,
            coordinateReversal observation.coordinate)

/-- No generated analytic zero can be installed as a late point of an
existing finite formal determinant zero fibre. -/
theorem isEmpty_localBlockZeroFiberSpecialization {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (stage : Nat) :
    IsEmpty (LocalBlockZeroFiberSpecialization observation stage) := by
  constructor
  intro specialization
  let polynomial :=
    (GlobalBlockDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial
  have killed :
      algebraMap BlockCoordinateRing
          (LocalGeneratedBlockZeroFiberRing stage)
          (blockDeterminantSection seedOccurrence.root stage) = 0 := by
    change AdjoinRoot.mk polynomial
        (Polynomial.C
          (blockDeterminantSection seedOccurrence.root stage)) = 0
    rw [← globalBlockSection_local_restriction stage]
    exact AdjoinRoot.mk_self
  have evaluated := congrArg specialization.map killed
  rw [map_zero,
    specialization.extendsEvaluation
      (blockDeterminantSection seedOccurrence.root stage)] at evaluated
  exact observation.finiteBlockDeterminant_ne_zero stage evaluated

end GeneratedRiemannZeroObservationAt

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
