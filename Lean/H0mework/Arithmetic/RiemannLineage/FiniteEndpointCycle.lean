import H0mework.Arithmetic.EulerDerived.PointActualDatum
import H0mework.Arithmetic.EulerAnalytic.TautologicalReadback

/-!
# Finite q-rich endpoint cycles from actual factor rows

The actual factorial occurrence supplies both whole and quotient
coefficients.  Filling every role with those coefficients produces a strict
cycle, unlike the historical raw endpoint with zero quotient roles.  The two
source-owned basis orientations are generated internally; arbitrary bases
remain ordinary mathematical inputs and carry no authority.
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
namespace QRich

open CategoryTheory
open CochainComplex.HomComplex
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom

noncomputable section

def blockQuotientAntiInvariantProjection (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockInner seedOccurrence.root stage :=
  (blockInnerAntiInvariant seedOccurrence.root stage).comp
    (LinearMap.proj (some row))

/-- Whole and every quotient role are filled from the same factorial fold. -/
def blockQRichEndpointVertexMap (stage : Nat) :
    BlockDualBase →ₗ[BlockCoordinateRing]
      BlockWholeVertex seedOccurrence.root stage where
  toFun base role index :=
    match role with
    | none =>
        (wholeCoefficient seedOccurrence.root stage : BlockCoordinateRing) *
          base index.2
    | some row =>
        (quotientCoefficient row : BlockCoordinateRing) * base index.2
  map_add' left right := by
    funext role index
    cases role <;> simp only [Pi.add_apply] <;> ring
  map_smul' scalar base := by
    funext role index
    cases role <;>
      simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] <;> ring

/-- The q-rich endpoint is a literal strict cycle of the full actual
factorization complex. -/
theorem blockQRichEndpointVertexMap_differential_zero
    (stage : Nat) (base : BlockDualBase) :
    blockFactorizationDifferential seedOccurrence.root stage
        (blockQRichEndpointVertexMap stage base) = 0 := by
  funext row index
  have coefficientNat :=
    wholeCoefficient_eq_primePower_mul_quotientCoefficient
      seedOccurrence.root stage row
  have coefficient :
      (wholeCoefficient seedOccurrence.root stage : BlockCoordinateRing) =
        (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) *
          (quotientCoefficient row : BlockCoordinateRing) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun value : Nat => (value : BlockCoordinateRing))
        coefficientNat
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockFactorizationDifferential, blockQRichEndpointVertexMap,
      blockInnerAntiInvariant, blockInnerReversal] <;>
    rw [coefficient] <;> ring

theorem blockQRichEndpoint_wholeAntiInvariant (stage : Nat)
    (base : BlockDualBase) (index : BaseIndex seedOccurrence.root stage) :
    blockWholeAntiInvariantProjection stage
        (blockQRichEndpointVertexMap stage base) index =
      (wholeCoefficient seedOccurrence.root stage : BlockCoordinateRing) *
        (base index.2 - base index.2.rev) := by
  simp [blockWholeAntiInvariantProjection, blockInnerAntiInvariant,
    blockInnerReversal, blockQRichEndpointVertexMap]
  ring

theorem blockQRichEndpoint_quotientAntiInvariant (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) (base : BlockDualBase)
    (index : BaseIndex seedOccurrence.root stage) :
    blockQuotientAntiInvariantProjection stage row
        (blockQRichEndpointVertexMap stage base) index =
      (quotientCoefficient row : BlockCoordinateRing) *
        (base index.2 - base index.2.rev) := by
  simp [blockQuotientAntiInvariantProjection, blockInnerAntiInvariant,
    blockInnerReversal, blockQRichEndpointVertexMap]
  ring

theorem blockQRichEndpoint_primePower_landing (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) (base : BlockDualBase) :
    blockWholeAntiInvariantProjection stage
        (blockQRichEndpointVertexMap stage base) =
      (rowPrime row : Nat) ^ rowExponent row •
        blockQuotientAntiInvariantProjection stage row
          (blockQRichEndpointVertexMap stage base) := by
  have differential : blockWholeAntiInvariantProjection stage
        (blockQRichEndpointVertexMap stage base) -
      (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
        blockQuotientAntiInvariantProjection stage row
          (blockQRichEndpointVertexMap stage base) = 0 := by
    simpa [blockFactorizationDifferential,
      blockWholeAntiInvariantProjection,
      blockQuotientAntiInvariantProjection] using congrFun
        (blockQRichEndpointVertexMap_differential_zero stage base) row
  have landing := sub_eq_zero.mp differential
  simpa only [← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul] using landing

theorem blockQRichEndpoint_quotientZero (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) (base : BlockDualBase) :
    PrimePowerQuotientEvaluation.evaluator
        (BlockInner seedOccurrence.root stage)
        (blockWholeAntiInvariantProjection stage
          (blockQRichEndpointVertexMap stage base))
        (rowPrime row) (rowExponent row) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff
    (blockWholeAntiInvariantProjection stage
      (blockQRichEndpointVertexMap stage base))).2
  exact ⟨blockQuotientAntiInvariantProjection stage row
      (blockQRichEndpointVertexMap stage base),
    (blockQRichEndpoint_primePower_landing stage row base).symm⟩

def blockQRichSuccessorScale (stage : Nat) : Nat :=
  (StageHistory seedOccurrence.root stage).cardinalShadow + 1

theorem blockQRichWholeCoefficient_successor (stage : Nat) :
    wholeCoefficient seedOccurrence.root (stage + 1) =
      blockQRichSuccessorScale stage *
        wholeCoefficient seedOccurrence.root stage := by
  unfold wholeCoefficient blockQRichSuccessorScale
  rw [factorialHistory_cardinalShadow, factorialHistory_cardinalShadow,
    stageHistory_succ]
  change Nat.factorial
      (Nat.succ (StageHistory seedOccurrence.root stage).cardinalShadow) =
    ((StageHistory seedOccurrence.root stage).cardinalShadow + 1) *
      Nat.factorial (StageHistory seedOccurrence.root stage).cardinalShadow
  rw [Nat.factorial_succ]

theorem blockQRichQuotientCoefficient_lift (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    quotientCoefficient (liftFactorRow seedOccurrence.root stage row) =
      blockQRichSuccessorScale stage * quotientCoefficient row := by
  have high := wholeCoefficient_eq_primePower_mul_quotientCoefficient
    seedOccurrence.root (stage + 1)
      (liftFactorRow seedOccurrence.root stage row)
  have low := wholeCoefficient_eq_primePower_mul_quotientCoefficient
    seedOccurrence.root stage row
  rw [liftFactorRow_prime, liftFactorRow_exponent] at high
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.pow_pos (rowPrime row).property.pos)
  calc
    (rowPrime row : Nat) ^ rowExponent row *
        quotientCoefficient (liftFactorRow seedOccurrence.root stage row) =
      wholeCoefficient seedOccurrence.root (stage + 1) := high.symm
    _ = blockQRichSuccessorScale stage *
        wholeCoefficient seedOccurrence.root stage :=
      blockQRichWholeCoefficient_successor stage
    _ = blockQRichSuccessorScale stage *
        ((rowPrime row : Nat) ^ rowExponent row *
          quotientCoefficient row) := by rw [low]
    _ = (rowPrime row : Nat) ^ rowExponent row *
        (blockQRichSuccessorScale stage * quotientCoefficient row) := by
      ac_rfl

theorem blockQRichQuotientCoefficient_ne_zero (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    quotientCoefficient row ≠ 0 := by
  intro quotientZero
  have coefficient :=
    wholeCoefficient_eq_primePower_mul_quotientCoefficient
      seedOccurrence.root stage row
  rw [quotientZero, Nat.mul_zero] at coefficient
  have wholeNe : wholeCoefficient seedOccurrence.root stage ≠ 0 := by
    unfold wholeCoefficient
    rw [factorialHistory_cardinalShadow]
    exact Nat.factorial_ne_zero _
  exact wholeNe coefficient

theorem blockQRichEndpointVertexMap_restriction_scale (stage : Nat) :
    (blockWholeVertexRestriction seedOccurrence.root stage).comp
        (blockQRichEndpointVertexMap (stage + 1)) =
      (blockQRichSuccessorScale stage : BlockCoordinateRing) •
        blockQRichEndpointVertexMap stage := by
  apply LinearMap.ext
  intro base
  funext role index
  cases role with
  | none =>
      change
        (wholeCoefficient seedOccurrence.root (stage + 1) :
            BlockCoordinateRing) * base index.2 =
          (blockQRichSuccessorScale stage : BlockCoordinateRing) *
            ((wholeCoefficient seedOccurrence.root stage :
              BlockCoordinateRing) * base index.2)
      rw [blockQRichWholeCoefficient_successor]
      push_cast
      ring
  | some row =>
      change
        (quotientCoefficient
            (liftFactorRow seedOccurrence.root stage row) :
              BlockCoordinateRing) * base index.2 =
          (blockQRichSuccessorScale stage : BlockCoordinateRing) *
            ((quotientCoefficient row : BlockCoordinateRing) * base index.2)
      rw [blockQRichQuotientCoefficient_lift]
      push_cast
      ring

/-- Corrected derived point generated from the strict q-rich cycle itself. -/
noncomputable def localQRichDerivedPoint (stage : Nat)
    (base : BlockDualBase) :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶ LocalDerivedSolution stage :=
  localCorrectedEndpointPoint stage
    (blockQRichEndpointVertexMap stage base)

theorem localQRichSourceEndpointBoundaryCycle_eq_zero (stage : Nat)
    (base : BlockDualBase) :
    localSourceEndpointBoundaryCycle stage
        (blockQRichEndpointVertexMap stage base) = 0 := by
  apply (ModuleCat.mono_iff_injective
    ((LocalWholeComplex stage).iCycles 1)).mp inferInstance
  rw [map_zero, localSourceEndpointBoundaryCycle_underlying]
  exact blockQRichEndpointVertexMap_differential_zero stage base

theorem localQRichDerivedPoint_strictSource_zero (stage : Nat)
    (base : BlockDualBase) :
    localDerivedStrictSource stage (localQRichDerivedPoint stage base) = 0 := by
  rw [localQRichDerivedPoint, localCorrectedEndpoint_strictSource,
    localQRichSourceEndpointBoundaryCycle_eq_zero]
  apply Cochain.ofHom_injective
  have representation :
      Cochain.ofHom
          (CochainMappingCoconeMappedBoundaryAtomOver.cycleMorphism
            (0 : (LocalWholeComplex stage).cycles 1)) =
        Cochain.fromSingleMk
          (CochainMappingCoconeMappedBoundaryAtomOver.cycleGenerator
            (0 : (LocalWholeComplex stage).cycles 1)) (by norm_num) := by
    unfold CochainMappingCoconeMappedBoundaryAtomOver.cycleMorphism
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  rw [representation]
  have generatorZero :
      CochainMappingCoconeMappedBoundaryAtomOver.cycleGenerator
          (0 : (LocalWholeComplex stage).cycles 1) = 0 := by
    unfold CochainMappingCoconeMappedBoundaryAtomOver.cycleGenerator
    rw [CochainMappingCoconeMappedBoundaryAtomOver.elementHom_zero,
      Limits.zero_comp]
  rw [generatorZero, Cochain.fromSingleMk_zero]
  rw [Cochain.ofHom_zero]

theorem localQRichDerivedPoint_endpointCochain (stage : Nat)
    (base : BlockDualBase) :
    (localDerivedEndpointCochain stage
        (localQRichDerivedPoint stage base)).v 1 0 (by omega)
          scalarSingleOneGenerator =
      -blockQRichEndpointVertexMap stage base := by
  exact localCorrectedEndpoint_endpointCochain stage
    (blockQRichEndpointVertexMap stage base)

noncomputable def localLeftQRichDerivedPoint (stage : Nat) :=
  localQRichDerivedPoint stage blockLeftEndpointBase

noncomputable def localRightQRichDerivedPoint (stage : Nat) :=
  localQRichDerivedPoint stage blockRightEndpointBase

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
