import H0mework.NavierStokes.Accumulation.WholeReceiptKineticTimeModulus
import H0mework.Versions.X.NavierStokes.Accumulation.NativeFluidMediumRoot

/-!
# Kinetic valuation of one standing arithmetic material

The root residual expansion already records the actual source/target rows,
contact clock and finite fresh-gain inventory of one standing-valued
material.  This file identifies its quantitative payment directly with the
cutoff-free kinetic Euler row of that same occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus

noncomputable section

/-- Every source-generated positive kinetic row in the live standing cube is
definitionally one of the same residual expansion's fresh-gain rows. -/
theorem NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.kineticPayingModes_subset_physicalModes
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : material.GeneratedResidualExpansionAt residual)
    (modes : Finset IntegerWavevector)
    (modesInStanding :
      modes ⊆ wholeRestartModes (standing.anchorLevel + 1))
    (densityPositive : ∀ wave ∈ modes,
      0 < nextContactKineticEulerPaymentDensity current wave) :
    modes ⊆ expansion.physicalModes := by
  intro wave waveMem
  have waveInStanding := modesInStanding waveMem
  have waveNe : wave ≠ 0 := by
    intro waveZero
    subst wave
    exact (zero_not_mem_puncturedIntegerWaveFrequencyCube _) waveInStanding
  have rowLower :=
    nextContact_amplitudeSq_sub_current_le_from_below_kineticSource
      current wave waveNe
  have clockTimesDensityPos :
      0 < current.nextContact.time.1 *
        nextContactKineticEulerPaymentDensity current wave :=
    mul_pos current.nextContact.time_pos
      (densityPositive wave waveMem)
  have actualGain :
      complexCoordinateAmplitudeSq
          (current.contact.physicalState wave) <
        complexCoordinateAmplitudeSq
          (current.nextContact.physicalState wave) := by
    linarith
  rw [expansion.physicalModes_eq]
  apply Finset.mem_filter.mpr
  refine ⟨waveInStanding, ?_⟩
  rw [material.rawValuedMaterial.sourcePhysicalState_eq,
    material.rawValuedMaterial.targetPhysicalState_eq]
  change
    complexCoordinateAmplitudeSq
        (current.contact.physicalState wave) <
      complexCoordinateAmplitudeSq
        (current.nextContact.physicalState wave)
  exact actualGain

/-- The Real valuation of one residual expansion dominates the exact clock
times the summed kinetic density of any internally paying finite face.  The
arithmetic residual, physical gain and clock therefore remain projections
of one provenance; no scalar payment can be paired with another edge. -/
theorem NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.clock_mul_sum_kineticDensity_le_finiteNetEnstrophyDebit
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : material.GeneratedResidualExpansionAt residual)
    (modes : Finset IntegerWavevector)
    (modesInStanding :
      modes ⊆ wholeRestartModes (standing.anchorLevel + 1))
    (densityPositive : ∀ wave ∈ modes,
      0 < nextContactKineticEulerPaymentDensity current wave) :
    current.nextContact.time.1 *
        (∑ wave ∈ modes,
          nextContactKineticEulerPaymentDensity current wave) ≤
      expansion.finiteNetEnstrophyDebit := by
  have modesSubset : modes ⊆ expansion.physicalModes :=
    NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.kineticPayingModes_subset_physicalModes
      expansion modes modesInStanding densityPositive
  let rowGain : IntegerWavevector → Real := fun wave =>
    complexCoordinateAmplitudeSq
        (material.rawValuedMaterial.targetPhysicalState wave) -
      complexCoordinateAmplitudeSq
        (material.rawValuedMaterial.sourcePhysicalState wave)
  have rowGainNonneg : ∀ wave ∈ expansion.physicalModes,
      0 ≤ rowGain wave := by
    intro wave waveMem
    have freshMem : wave ∈
        NativeRestartStandingValuedArithmeticMaterialAt.standingValuedFreshGainModes
          material := by
      rw [← expansion.physicalModes_eq]
      exact waveMem
    exact sub_nonneg.mpr (Finset.mem_filter.mp freshMem).2.le
  have kineticLeGain : ∀ wave ∈ modes,
      current.nextContact.time.1 *
          nextContactKineticEulerPaymentDensity current wave ≤
        rowGain wave := by
    intro wave waveMem
    have waveInStanding := modesInStanding waveMem
    have waveNe : wave ≠ 0 := by
      intro waveZero
      subst wave
      exact (zero_not_mem_puncturedIntegerWaveFrequencyCube _) waveInStanding
    have generated :=
      nextContact_amplitudeSq_sub_current_le_from_below_kineticSource
        current wave waveNe
    dsimp only [rowGain]
    rw [material.rawValuedMaterial.sourcePhysicalState_eq,
      material.rawValuedMaterial.targetPhysicalState_eq]
    change
      current.nextContact.time.1 *
          nextContactKineticEulerPaymentDensity current wave ≤
        complexCoordinateAmplitudeSq
            (current.nextContact.physicalState wave) -
          complexCoordinateAmplitudeSq
            (current.contact.physicalState wave)
    exact generated
  have summedKinetic :
      (∑ wave ∈ modes,
          current.nextContact.time.1 *
            nextContactKineticEulerPaymentDensity current wave) ≤
        ∑ wave ∈ modes, rowGain wave := by
    apply Finset.sum_le_sum
    intro wave waveMem
    exact kineticLeGain wave waveMem
  have summedGain :
      (∑ wave ∈ modes, rowGain wave) ≤
        ∑ wave ∈ expansion.physicalModes, rowGain wave := by
    exact Finset.sum_le_sum_of_subset_of_nonneg modesSubset
      (fun wave waveMem _waveNotMem => rowGainNonneg wave waveMem)
  rw [Finset.mul_sum]
  calc
    (∑ wave ∈ modes,
        current.nextContact.time.1 *
          nextContactKineticEulerPaymentDensity current wave) ≤
        ∑ wave ∈ modes, rowGain wave := summedKinetic
    _ ≤ ∑ wave ∈ expansion.physicalModes, rowGain wave := summedGain
    _ = expansion.finiteNetEnstrophyDebit := by
      rw [expansion.finiteNetEnstrophyDebit_eq]
      unfold finiteStateVorticityCoefficientEnstrophy
      dsimp only [rowGain]
      rw [Finset.sum_sub_distrib]

/-! ## Same-material kinetic-face advance -/

/-- The compiler-selected endpoint tangent differs from the current tangent
by at most the cutoff-free source upper generated by the same full replay. -/
theorem nextContact_tangent_sub_current_norm_le_kineticSource
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ‖wholeLatticeVorticityFourierTangentAt nu.coeff
          current.nextContact.physicalState wave -
        wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave‖ ≤
      fullReplayKineticTangentSourceUpper current wave := by
  let receipt := current.nextReceipt
  let actual := current.nextContact.time.1
  let pathState : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  have pathStateEq : pathState = current.nextContact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc 0 (wholeRestartDuration current.contact)
          (wholeRestartDuration_pos current.contact).le actual) =
      current.nextContact.physicalState
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos current.contact).le
      current.nextContact.time.2]
    rfl
  have heatPathEq :
      actualWholeContinuousHeatDuhamelPath receipt wave actual =
        current.nextContact.physicalState wave := by
    exact (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      receipt wave waveNe current.nextContact.time).symm
  have actualLe :=
    fullReplayEulerErrorDerivative_norm_le_kinetic
      current wave waveNe actual current.nextContact.time.2
  have sourceLe :=
    fullReplayKineticTangentDriftUpper_le_sourceUpper current wave
  unfold fullReplayEulerErrorDerivative at actualLe
  rw [heatPathEq, ← pathStateEq] at actualLe
  change
    ‖wholeLatticeVorticityFourierTangentAt nu.coeff pathState wave -
        wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave‖ ≤
      fullReplayKineticTangentDriftUpper current wave at actualLe
  rw [pathStateEq] at actualLe
  exact actualLe.trans sourceLe

/-- The selected endpoint row has one linear-in-clock displacement bound.
Both the Euler term and its remainder are generated by the same replay. -/
theorem nextContact_row_sub_current_norm_le_kineticSource
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ‖current.nextContact.physicalState wave -
        current.contact.physicalState wave‖ ≤
      current.nextContact.time.1 *
        (‖wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave‖ +
          fullReplayKineticTangentSourceUpper current wave) := by
  let source := current.contact.physicalState wave
  let tangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let error := current.nextContact.physicalState wave -
    fullReplayEulerRow current current.nextContact.time.1 wave
  have errorLe :
      ‖error‖ ≤ current.nextContact.time.1 *
        fullReplayKineticTangentSourceUpper current wave := by
    change
      ‖current.nextReceipt.wholePath current.nextContact.time wave -
          fullReplayEulerRow current current.nextContact.time.1 wave‖ ≤ _
    exact fullReplay_row_sub_euler_norm_le_kineticSource
      current wave waveNe current.nextContact.time
  have decomposition :
      current.nextContact.physicalState wave - source =
        current.nextContact.time.1 • tangent + error := by
    dsimp only [source, tangent, error]
    unfold fullReplayEulerRow
    module
  rw [decomposition]
  calc
    ‖current.nextContact.time.1 • tangent + error‖ ≤
        ‖current.nextContact.time.1 • tangent‖ + ‖error‖ :=
      norm_add_le _ _
    _ ≤ current.nextContact.time.1 * ‖tangent‖ +
          current.nextContact.time.1 *
            fullReplayKineticTangentSourceUpper current wave := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos current.nextContact.time_pos]
      exact add_le_add le_rfl errorLe
    _ = current.nextContact.time.1 *
        (‖wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave‖ +
          fullReplayKineticTangentSourceUpper current wave) := by
      dsimp only [tangent]
      ring

/-- Current-side kinetic work of one actual Fourier row. -/
def kineticSelfTangentWorkAt
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : Real :=
  complexCoordinateRealInner (state wave)
    (wholeLatticeVorticityFourierTangentAt nu.coeff state wave)

theorem fullReplayKineticTangentSourceUpper_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    0 ≤ fullReplayKineticTangentSourceUpper current wave := by
  let angular := (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)
  let damping := nu.coeff * integerWaveViscousMultiplier wave
  have angularNonneg : 0 ≤ angular := by
    dsimp only [angular]
    positivity
  have dampingNonneg : 0 ≤ damping := by
    dsimp only [damping]
    unfold integerWaveViscousMultiplier
    exact mul_nonneg nu.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have coefficientNonneg :
      0 ≤ angular * (2 * fullReplayKineticVelocityRadius current) +
        damping := by
    exact add_nonneg
      (mul_nonneg angularNonneg
        (mul_nonneg (by norm_num)
          (fullReplayKineticVelocityRadius_nonneg current)))
      dampingNonneg
  unfold fullReplayKineticTangentSourceUpper
  dsimp only [angular, damping] at angularNonneg coefficientNonneg ⊢
  exact mul_nonneg angularNonneg
    (mul_nonneg coefficientNonneg (Real.sqrt_nonneg _))

/-- Exact current-side loss budget for transporting one kinetic paying row
through this standing-valued material's compiler-owned edge. -/
def standingValuedKineticFaceAdvanceLossUpper
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (wave : IntegerWavevector) : Real :=
  let sourceTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let tangentDrift := fullReplayKineticTangentSourceUpper current wave
  3 * (material.contactTime * (‖sourceTangent‖ + tangentDrift)) *
      (‖sourceTangent‖ + tangentDrift) +
    3 * ‖current.contact.physicalState wave‖ * tangentDrift

theorem standingValuedKineticFaceAdvanceLossUpper_nonneg
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (wave : IntegerWavevector) :
    0 ≤ standingValuedKineticFaceAdvanceLossUpper material wave := by
  unfold standingValuedKineticFaceAdvanceLossUpper
  let tangentDrift := fullReplayKineticTangentSourceUpper current wave
  have tangentDriftNonneg : 0 ≤ tangentDrift := by
    exact fullReplayKineticTangentSourceUpper_nonneg current wave
  have sumNonneg : 0 ≤
      ‖wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave‖ + tangentDrift :=
    add_nonneg (norm_nonneg _) tangentDriftNonneg
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg material.contactTime_pos.le sumNonneg))
      sumNonneg)
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (norm_nonneg (current.contact.physicalState wave)))
      tangentDriftNonneg)

/-- Arithmetic provenance, Real valuation and kinetic face transport are one
edge: the actual self-work change is bounded by the loss computed from this
same standing-valued material. -/
theorem abs_next_selfTangentWork_sub_current_le_standingValuedLoss
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    |kineticSelfTangentWorkAt nu current.nextContact.physicalState wave -
        kineticSelfTangentWorkAt nu current.contact.physicalState wave| ≤
      standingValuedKineticFaceAdvanceLossUpper material wave := by
  let sourceState := current.contact.physicalState wave
  let targetState := current.nextContact.physicalState wave
  let sourceTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let targetTangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.nextContact.physicalState wave
  let tangentDrift := fullReplayKineticTangentSourceUpper current wave
  have tangentDriftNonneg : 0 ≤ tangentDrift := by
    exact fullReplayKineticTangentSourceUpper_nonneg current wave
  have rowLe : ‖targetState - sourceState‖ ≤
      current.nextContact.time.1 * (‖sourceTangent‖ + tangentDrift) := by
    simpa only [sourceState, targetState, sourceTangent, tangentDrift] using
      nextContact_row_sub_current_norm_le_kineticSource
        current wave waveNe
  have tangentLe : ‖targetTangent - sourceTangent‖ ≤ tangentDrift := by
    simpa only [sourceTangent, targetTangent, tangentDrift] using
      nextContact_tangent_sub_current_norm_le_kineticSource
        current wave waveNe
  have targetTangentLe : ‖targetTangent‖ ≤
      ‖sourceTangent‖ + tangentDrift := by
    calc
      ‖targetTangent‖ = ‖(targetTangent - sourceTangent) + sourceTangent‖ := by
        congr 1
        module
      _ ≤ ‖targetTangent - sourceTangent‖ + ‖sourceTangent‖ :=
        norm_add_le _ _
      _ ≤ tangentDrift + ‖sourceTangent‖ :=
        by linarith
      _ = ‖sourceTangent‖ + tangentDrift := add_comm _ _
  have pairing := abs_complexCoordinateRealInner_pair_sub_le
    targetState sourceState targetTangent sourceTangent
  have advanceFactorNonneg :
      0 ≤ current.nextContact.time.1 *
        (‖sourceTangent‖ + tangentDrift) :=
    mul_nonneg current.nextContact.time_pos.le
      (add_nonneg (norm_nonneg _) tangentDriftNonneg)
  have targetBoundNonneg : 0 ≤ ‖sourceTangent‖ + tangentDrift :=
    add_nonneg (norm_nonneg _) tangentDriftNonneg
  have firstLe :
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ ≤
        3 * (current.nextContact.time.1 *
          (‖sourceTangent‖ + tangentDrift)) *
            (‖sourceTangent‖ + tangentDrift) := by
    calc
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ ≤
          3 * (current.nextContact.time.1 *
            (‖sourceTangent‖ + tangentDrift)) * ‖targetTangent‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left rowLe (by norm_num))
          (norm_nonneg _)
      _ ≤ 3 * (current.nextContact.time.1 *
            (‖sourceTangent‖ + tangentDrift)) *
              (‖sourceTangent‖ + tangentDrift) :=
        mul_le_mul_of_nonneg_left targetTangentLe
          (mul_nonneg (by norm_num) advanceFactorNonneg)
  have secondLe :
      3 * ‖sourceState‖ * ‖targetTangent - sourceTangent‖ ≤
        3 * ‖sourceState‖ * tangentDrift :=
    mul_le_mul_of_nonneg_left tangentLe
      (mul_nonneg (by norm_num) (norm_nonneg _))
  unfold kineticSelfTangentWorkAt
  dsimp only [targetState, sourceState, targetTangent, sourceTangent]
    at pairing ⊢
  calc
    |_ - _| ≤
        3 * ‖current.nextContact.physicalState wave -
              current.contact.physicalState wave‖ *
            ‖wholeLatticeVorticityFourierTangentAt nu.coeff
              current.nextContact.physicalState wave‖ +
          3 * ‖current.contact.physicalState wave‖ *
            ‖wholeLatticeVorticityFourierTangentAt nu.coeff
                current.nextContact.physicalState wave -
              wholeLatticeVorticityFourierTangentAt nu.coeff
                current.contact.physicalState wave‖ := pairing
    _ ≤
        3 * (current.nextContact.time.1 *
              (‖wholeLatticeVorticityFourierTangentAt nu.coeff
                    current.contact.physicalState wave‖ +
                fullReplayKineticTangentSourceUpper current wave)) *
            (‖wholeLatticeVorticityFourierTangentAt nu.coeff
                  current.contact.physicalState wave‖ +
              fullReplayKineticTangentSourceUpper current wave) +
          3 * ‖current.contact.physicalState wave‖ *
            fullReplayKineticTangentSourceUpper current wave := by
      simpa only [sourceState, targetState, sourceTangent, targetTangent,
        tangentDrift] using add_le_add firstLe secondLe
    _ = standingValuedKineticFaceAdvanceLossUpper material wave := by
      unfold standingValuedKineticFaceAdvanceLossUpper
      rfl

/-- A finite current-side reserve transports the paying instruction to the
compiler-owned successor.  No future state or recurrence witness is an input. -/
theorem next_selfTangentWork_gt_of_standingValuedReserve
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (reserve : 1 + standingValuedKineticFaceAdvanceLossUpper material wave <
      kineticSelfTangentWorkAt nu current.contact.physicalState wave) :
    1 < kineticSelfTangentWorkAt nu
      current.nextContact.physicalState wave := by
  have bounded :=
    abs_next_selfTangentWork_sub_current_le_standingValuedLoss
      material wave waveNe
  have lower := neg_abs_le
    (kineticSelfTangentWorkAt nu current.nextContact.physicalState wave -
      kineticSelfTangentWorkAt nu current.contact.physicalState wave)
  linarith

end

end ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
end NavierStokes
end SaturationMonoid
