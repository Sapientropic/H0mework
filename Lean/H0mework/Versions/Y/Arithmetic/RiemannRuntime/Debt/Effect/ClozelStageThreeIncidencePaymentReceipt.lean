import H0mework.Versions.Y.Arithmetic.RiemannRuntime.Controller.ClozelPairedRieszEnergySupportBranchNeutralDebtGate
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Coupling.Relation.LivingLawCanonicalRiemannStageThreeArithmeticMellinActionBoundary
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Topology.Measurement.LivingLawCanonicalRiemannPrimeExponentPoleEnergyMellinAction

/-!
# Stage-three incidence payment receipt

The branch-neutral receipt root already emits the prime-three action boundary.
On an expanding sibling, that exact boundary has a nonzero Mellin incidence.
This file records the source boundary, its root measurement/effect writes and
the nonzero incidence in one proof-relevant receipt.  The receipt is generated
only after the root has selected its total critical/off-center disposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate

open Character.GlobalCoPoissonCurrent
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerCrossPrimeRestrictionObstruction
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open AllPlace.ActionCofiber.RawEffect
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.EnergyCompletion
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character.CommonAction
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character.CommonAction.Boundary

noncomputable section

theorem stageThreePrimeExponent_energyScale_eq :
    scaleSquare
      (primeExponentScale (Multiplicative.toAdd stageThreePrimeExponent)) = 9 := by
  rw [stageThreePrimeExponent_scale]
  have rowPrimeEq : rowPrime actualStageThreePrimeRow = PrimeThree := by
    apply Subtype.ext
    exact actualStageThreePrimeRow_prime
  rw [rowPrimeEq]
  norm_num [scaleSquare, scaleValue, blockPrimeScaleUnit,
    SourceGeneratedPositiveRealCharacter.positiveRealUnit_val]

theorem selectedStageThreeMellinCharacter_norm_gt_one
    (observation : GeneratedRiemannZeroObservation)
    (left : observation.coordinate.re < 1 / 2) :
    1 < ‖selectedStageThreeMellinCharacter observation‖ := by
  unfold selectedStageThreeMellinCharacter primeExponentMellinCharacter
  change 1 < ‖quarterDilationCharacter
      (selectedCoPoissonMuntzParameter observation)
      (scaleSquare
        (primeExponentScale
          (Multiplicative.toAdd stageThreePrimeExponent)))‖
  unfold quarterDilationCharacter
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by
    rw [stageThreePrimeExponent_energyScale_eq]
    norm_num)]
  have scaleGt : 1 < scaleSquare
      (primeExponentScale
        (Multiplicative.toAdd stageThreePrimeExponent)) := by
    rw [stageThreePrimeExponent_energyScale_eq]
    norm_num
  have exponentPos :
      0 < ((1 / 4 : ℂ) -
        selectedCoPoissonMuntzParameter observation).re := by
    norm_num [selectedCoPoissonMuntzParameter]
    linarith
  have strict := (Real.strictMono_rpow_of_base_gt_one scaleGt) exponentPos
  simpa using strict

theorem reversalStageThreeMellinCharacter_norm_gt_one
    (observation : GeneratedRiemannZeroObservation)
    (right : 1 / 2 < observation.coordinate.re) :
    1 < ‖reversalStageThreeMellinCharacter observation‖ := by
  unfold reversalStageThreeMellinCharacter primeExponentMellinCharacter
  change 1 < ‖quarterDilationCharacter
      (reversalCoPoissonMuntzParameter observation)
      (scaleSquare
        (primeExponentScale
          (Multiplicative.toAdd stageThreePrimeExponent)))‖
  unfold quarterDilationCharacter
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by
    rw [stageThreePrimeExponent_energyScale_eq]
    norm_num)]
  have scaleGt : 1 < scaleSquare
      (primeExponentScale
        (Multiplicative.toAdd stageThreePrimeExponent)) := by
    rw [stageThreePrimeExponent_energyScale_eq]
    norm_num
  have exponentPos :
      0 < ((1 / 4 : ℂ) -
        reversalCoPoissonMuntzParameter observation).re := by
    norm_num [reversalCoPoissonMuntzParameter, coordinateReversal]
    linarith
  have strict := (Real.strictMono_rpow_of_base_gt_one scaleGt) exponentPos
  simpa using strict

theorem selectedStageThreeBoundaryMellin_eq_one_sub_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    (pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      stageThreeConductorIndex).1 =
        1 - selectedStageThreeMellinCharacter observation := by
  change selectedPrimeExponentPoleMellinMap observation nontrivial
      (factorizationBoundaryValue stageThreeConductorIndex) = _
  rw [selectedPrimeExponentPoleMellin_boundaryValue]
  unfold selectedStageThreeMellinCharacter primeExponentMellinCharacter
  change 1 - quarterDilationCharacter _
      (scaleSquare (primePowerUnit stageThreeConductorIndex.1
        stageThreeConductorIndex.2.1)) =
    1 - quarterDilationCharacter _
      (scaleSquare (primeExponentScale
        (Multiplicative.toAdd stageThreePrimeExponent)))
  rw [stageThreePrimeExponent_toAdd, primeExponentScale_primePower]

theorem reversalStageThreeBoundaryMellin_eq_one_sub_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    (pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      stageThreeConductorIndex).2 =
        1 - reversalStageThreeMellinCharacter observation := by
  change reversalPrimeExponentPoleMellinMap observation nontrivial
      (factorizationBoundaryValue stageThreeConductorIndex) = _
  rw [reversalPrimeExponentPoleMellin_boundaryValue]
  unfold reversalStageThreeMellinCharacter primeExponentMellinCharacter
  change 1 - quarterDilationCharacter _
      (scaleSquare (primePowerUnit stageThreeConductorIndex.1
        stageThreeConductorIndex.2.1)) =
    1 - quarterDilationCharacter _
      (scaleSquare (primeExponentScale
        (Multiplicative.toAdd stageThreePrimeExponent)))
  rw [stageThreePrimeExponent_toAdd, primeExponentScale_primePower]

theorem selectedStageThreeBoundaryMellin_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    (pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      stageThreeConductorIndex).1 ≠ 0 := by
  rw [selectedStageThreeBoundaryMellin_eq_one_sub_character]
  intro differenceZero
  have characterOne : selectedStageThreeMellinCharacter observation = 1 :=
    (sub_eq_zero.mp differenceZero).symm
  have strict := selectedStageThreeMellinCharacter_norm_gt_one observation left
  rw [characterOne, norm_one] at strict
  exact (lt_irrefl 1) strict

theorem reversalStageThreeBoundaryMellin_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    (pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      stageThreeConductorIndex).2 ≠ 0 := by
  rw [reversalStageThreeBoundaryMellin_eq_one_sub_character]
  intro differenceZero
  have characterOne : reversalStageThreeMellinCharacter observation = 1 :=
    (sub_eq_zero.mp differenceZero).symm
  have strict := reversalStageThreeMellinCharacter_norm_gt_one observation right
  rw [characterOne, norm_one] at strict
  exact (lt_irrefl 1) strict

/-- The exact paired boundary emitted at the receipt-root current cannot be
zero on an off-center outcome. -/
theorem stageThreeBoundaryMellin_ne_zero_of_offCenter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      stageThreeConductorIndex ≠ 0 := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · intro pairZero
    apply selectedStageThreeBoundaryMellin_ne_zero
      observation nontrivial left
    exact congrArg Prod.fst pairZero
  · intro pairZero
    apply reversalStageThreeBoundaryMellin_ne_zero
      observation nontrivial right
    exact congrArg Prod.snd pairZero

/-- Proof-relevant first-payment effect.  All fields are coordinates of the
same stage-three receipt-root occurrence. -/
structure StageThreeIncidencePaymentReceiptAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  private mk ::
  outcome : MeasurementOnlyAt observation nontrivial
  boundary_is_receipt : type_of% stageThreeFactorizationActionBoundary_eq_receipt
  integral_root_read : type_of%
    (stageThreeActionBoundary_integralRootRead observation nontrivial)
  measurement_root_read : type_of%
    (stageThreeActionBoundary_measurementRootRead observation nontrivial)
  incidence_readback : type_of%
    (stageThreeJointMeasurement_actionBoundary_eq_incidence
      observation nontrivial)
  root_effect_write : type_of%
    (stageThreeJointMeasurement_rootEffect_write observation nontrivial)
  paired_incidence_ne_zero :
    pairedOmegaMeasurementResidual observation nontrivial
      (primePowerUnit stageThreeConductorIndex.1
        stageThreeConductorIndex.2.1) ≠ 0
  source_boundary_measurement_ne_zero :
    (arithmeticMellinJointMeasurement observation nontrivial
      stageThreeFactorizationActionBoundary).2 ≠ 0
  root_factorizes : type_of%
    (A1cEnergySupportReceiptRoot.installedFaces_factorize
      observation nontrivial)
  source_boundary_write : type_of%
    (stageThreeActionBoundary_receiptRootedWrite observation nontrivial)

private def paymentReceiptOfMeasurementOnly
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (outcome : MeasurementOnlyAt observation nontrivial) :
    StageThreeIncidencePaymentReceiptAt observation nontrivial := by
  have boundaryNe := stageThreeBoundaryMellin_ne_zero_of_offCenter
    observation nontrivial outcome.offCenter
  refine
    { outcome := outcome
      boundary_is_receipt := stageThreeFactorizationActionBoundary_eq_receipt
      integral_root_read :=
        stageThreeActionBoundary_integralRootRead observation nontrivial
      measurement_root_read :=
        stageThreeActionBoundary_measurementRootRead observation nontrivial
      incidence_readback :=
        stageThreeJointMeasurement_actionBoundary_eq_incidence
          observation nontrivial
      root_effect_write :=
        stageThreeJointMeasurement_rootEffect_write observation nontrivial
      paired_incidence_ne_zero := ?_
      source_boundary_measurement_ne_zero := ?_
      root_factorizes := outcome.root_factorizes
      source_boundary_write := outcome.source_boundary_write }
  · rw [← pairedPrimeExponentPoleBoundaryMellin_eq_incidence]
    exact boundaryNe
  · rw [stageThreeJointMeasurement_actionBoundary]
    exact boundaryNe

/-- Total neutral-root outcome after the actual stage-three projection has
been read.  The positive branch keeps its separator terminal; the negative
branch generates a nonzero source-incidence payment receipt. -/
inductive StageThreeProjectionDispositionAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  | supported (outcome : SupportedAt observation nontrivial)
  | payment
      (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)

def generateStageThreeProjectionDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    StageThreeProjectionDispositionAt observation nontrivial :=
  match BranchNeutralDebtGate.generate observation nontrivial with
  | .supported outcome => .supported outcome
  | .measurementOnly outcome =>
      .payment (paymentReceiptOfMeasurementOnly outcome)

/-- Deletion control: a critical exact occurrence cannot carry the generated
negative payment receipt. -/
theorem no_stageThreeIncidencePaymentReceipt_of_critical
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (critical : observation.coordinate.re = 1 / 2) :
    IsEmpty (StageThreeIncidencePaymentReceiptAt observation nontrivial) where
  false receipt := receipt.outcome.offCenter critical

end
end IntegralGraphJointAction.BranchNeutralDebtGate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.generateStageThreeProjectionDisposition
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.no_stageThreeIncidencePaymentReceipt_of_critical
