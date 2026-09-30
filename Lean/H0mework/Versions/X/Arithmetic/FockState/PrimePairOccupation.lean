import H0mework.Versions.X.Arithmetic.GoldbachFourier.EffectiveCoefficient
import H0mework.Versions.X.Arithmetic.FockDynamics.RootUpdate

/-!
# Exact-owner prime-pair occupation

The same source-generated prime field enters the coherent diagonal sector and
the ordered tensor square of `secondQuantizedState`.  Evaluating its particle
measurement at the exact even charge counts the ordered prime-pair fibre and
therefore equals the existing source-generated additive coefficient.

This is the wave/particle coupling readback, not a nonvanishing premise:
nonzero occupation remains exactly equivalent to the Goldbach fibre being
inhabited.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

open CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open SourceGeneratedFiniteEffectiveCoefficient

noncomputable section

def atomicTargetAmplitude (index : Nat) : ParentCarrier →ₗ[ℤ] ℤ :=
  (Finsupp.lapply (R := ℤ) (M := ℤ)
    (2 * (index + 1) : NNReal)).comp particleMeasurement

def atomicPrimePairOccupation (owner : GlobalParentOwner) (index : Nat) : ℤ :=
  atomicTargetAmplitude index
    (secondQuantizedState (ownerPrimeField owner index))

theorem particleMeasurement_secondQuantizedState
    (field : IntegralOneParticle) :
    particleMeasurement (secondQuantizedState field) =
      pairCharge (field ⊗ₜ[ℤ] field) := by
  simp [particleMeasurement, secondQuantizedState, diagonalInclusion,
    thetaInclusion, jThetaInclusion, pairInclusion, pairProjection]

theorem atomicPrimePairOccupation_eq_sum
    (owner : GlobalParentOwner) (index : Nat) :
    atomicPrimePairOccupation owner index =
      ∑ left : OwnerPrimeIndexAt owner index,
        ∑ right : OwnerPrimeIndexAt owner index,
          if left.1 + right.1 = 2 * (index + 1)
          then (1 : ℤ) else 0 := by
  classical
  have scale_eq (primeIndex : OwnerPrimeIndexAt owner index) :
      ((ownerPrimeScaleUnit primeIndex : Units NNReal) : NNReal) =
        primeIndex.1 := by
    apply NNReal.eq
    exact ownerPrimeScaleUnit_value primeIndex
  rw [atomicPrimePairOccupation, atomicTargetAmplitude,
    LinearMap.comp_apply, Finsupp.lapply_apply,
    particleMeasurement_secondQuantizedState]
  simp_rw [ownerPrimeField, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum, ownerPrimeOneParticle_eq_delta,
    pairCharge_delta_tmul_delta]
  simp_rw [pairChargeBasis, scale_eq]
  simp_rw [Finset.sum_apply']
  simp only [Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro left _leftMem
  apply Finset.sum_congr rfl
  intro right _rightMem
  rw [Finsupp.single_apply]
  split <;> rename_i equality
  · have arithmeticEquality :
        left.1 + right.1 = 2 * (index + 1) := by
      exact_mod_cast equality
    simp [arithmeticEquality]
  · have arithmeticInequality :
        left.1 + right.1 ≠ 2 * (index + 1) := by
      intro arithmeticEquality
      apply equality
      exact_mod_cast arithmeticEquality
    simp [arithmeticInequality]

private def ownerAdditiveCoordinateEvaluation
    (owner : GlobalParentOwner) (index : Nat)
    (candidate : OwnerPrimePairCandidateAt owner index) : Nat :=
  candidate.1.1 + candidate.2.1

private noncomputable def ownerGeneratedAdditiveCoefficient
    (owner : GlobalParentOwner) (index : Nat) : Nat :=
  effectiveCoefficient (ownerAdditiveCoordinateEvaluation owner index)
    (2 * (index + 1))

def ownerPrimeIndexEquivGenerated
    (owner : GlobalParentOwner) (index : Nat) :
    OwnerPrimeIndexAt owner index ≃
      CanonicalUnitArithmeticEffectiveAdditiveProducer.GeneratedPrimeIndexAt index where
  toFun primeIndex :=
    ⟨primeIndex.1, by
      simpa [ownerEvenTargetHistory, evenTargetHistoryAt_eq] using primeIndex.2⟩
  invFun primeIndex :=
    ⟨primeIndex.1, by
      rw [ownerEvenTargetHistory, evenTargetHistoryAt_eq]
      exact primeIndex.2⟩
  left_inv primeIndex := by apply Subtype.ext; rfl
  right_inv primeIndex := by apply Subtype.ext; rfl

def ownerPrimePairEquivGenerated
    (owner : GlobalParentOwner) (index : Nat) :
    OwnerPrimePairCandidateAt owner index ≃
      CanonicalUnitArithmeticEffectiveAdditiveProducer.GeneratedPrimePairCandidateAt index :=
  (ownerPrimeIndexEquivGenerated owner index).prodCongr
    (ownerPrimeIndexEquivGenerated owner index)

private abbrev OwnerCoordinateAdditiveFibreAt
    (owner : GlobalParentOwner) (index : Nat) :=
  SourceGeneratedEffectiveFibreDisposition.Fibre
    (ownerAdditiveCoordinateEvaluation owner index) (2 * (index + 1))

private def ownerCoordinateAdditiveFibreEquiv
    (owner : GlobalParentOwner) (index : Nat) :
    OwnerCoordinateAdditiveFibreAt owner index ≃
      CoordinateAdditiveFibreAt index where
  toFun fibre := by
    refine ⟨ownerPrimePairEquivGenerated owner index fibre.1, ?_⟩
    have landing := fibre.2
    change fibre.1.1.1 + fibre.1.2.1 = 2 * (index + 1) at landing
    rw [additiveCoordinateEvaluation_eq_pairSum]
    simpa [ownerPrimePairEquivGenerated, ownerPrimeIndexEquivGenerated,
      generatedPrimeCoordinate, generatedTargetCoordinate,
      CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetHistory_eq_generate]
      using landing
  invFun fibre := by
    refine ⟨(ownerPrimePairEquivGenerated owner index).symm fibre.1, ?_⟩
    have landing := fibre.2
    rw [additiveCoordinateEvaluation_eq_pairSum] at landing
    simpa [ownerAdditiveCoordinateEvaluation, ownerPrimePairEquivGenerated,
      ownerPrimeIndexEquivGenerated, generatedPrimeCoordinate,
      generatedTargetCoordinate,
      CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetHistory_eq_generate]
      using landing
  left_inv fibre := by apply Subtype.ext; rfl
  right_inv fibre := by apply Subtype.ext; rfl

private theorem atomicPrimePairOccupation_eq_ownerCoefficient
    (owner : GlobalParentOwner) (index : Nat) :
    atomicPrimePairOccupation owner index =
      (ownerGeneratedAdditiveCoefficient owner index : ℤ) := by
  rw [atomicPrimePairOccupation_eq_sum, ownerGeneratedAdditiveCoefficient,
    effectiveCoefficient_eq_card_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  push_cast
  rfl

private theorem ownerGeneratedAdditiveCoefficient_eq_generated
    (owner : GlobalParentOwner) (index : Nat) :
    ownerGeneratedAdditiveCoefficient owner index =
      generatedAdditiveCoefficient index := by
  calc
    ownerGeneratedAdditiveCoefficient owner index =
        Fintype.card (OwnerCoordinateAdditiveFibreAt owner index) :=
      effectiveCoefficient_eq_card_fibre _ _
    _ = Fintype.card (CoordinateAdditiveFibreAt index) :=
      Fintype.card_congr (ownerCoordinateAdditiveFibreEquiv owner index)
    _ = Fintype.card
        (CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveFibreAt index) :=
      Fintype.card_congr (coordinateEffectiveFibreEquiv index)
    _ = generatedAdditiveCoefficient index :=
      (generatedAdditiveCoefficient_eq_card_effectiveFibre index).symm

theorem atomicPrimePairOccupation_eq_generatedAdditiveCoefficient
    (owner : GlobalParentOwner) (index : Nat) :
    atomicPrimePairOccupation owner index =
      (generatedAdditiveCoefficient index : ℤ) := by
  calc
    atomicPrimePairOccupation owner index =
        (ownerGeneratedAdditiveCoefficient owner index : ℤ) :=
      atomicPrimePairOccupation_eq_ownerCoefficient owner index
    _ = (generatedAdditiveCoefficient index : ℤ) := by
      exact_mod_cast ownerGeneratedAdditiveCoefficient_eq_generated owner index

theorem atomicPrimePairOccupation_ne_zero_iff_coefficient_pos
    (owner : GlobalParentOwner) (index : Nat) :
    atomicPrimePairOccupation owner index ≠ 0 ↔
      0 < generatedAdditiveCoefficient index := by
  rw [atomicPrimePairOccupation_eq_generatedAdditiveCoefficient]
  omega

theorem atomicPrimePairOccupation_ne_zero_iff_effectiveFibre
    (owner : GlobalParentOwner) (index : Nat) :
    atomicPrimePairOccupation owner index ≠ 0 ↔
      Nonempty (EffectiveAdditiveFibreAt index) := by
  rw [atomicPrimePairOccupation_ne_zero_iff_coefficient_pos,
    generatedAdditiveCoefficient_pos_iff_effectiveFibre]

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
