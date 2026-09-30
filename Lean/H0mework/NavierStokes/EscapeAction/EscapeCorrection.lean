import H0mework.NavierStokes.EscapeAction.EscapeMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryEscapeCorrection

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress NativeRecoveryEscapeMomentum
open NativeStressSource NativeStressCurlAlgebra NativeCofinalStress NativeTimeJetCarrier
open NativeEndpointVelocityCarrier

noncomputable section

theorem projected_flux_eq_finite (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    quadraticFlux (complexSharpSupportProjection modes velocity) wave output input =
      -∑ first ∈ modes, (complexSharpSupportProjection modes velocity) first input *
        (complexSharpSupportProjection modes velocity) (wave - first) output := by
  unfold quadraticFlux
  congr 1
  apply tsum_eq_sum
  intro first outside
  simp [complexSharpSupportProjection_apply, outside]

theorem projected_flux_tendsto (modes : Finset IntegerWavevector) (sequence : ℕ → ComplexVorticityHilbertState)
    (limit : ComplexVorticityHilbertState)
    (rows : ∀ wave, Tendsto (fun index => sequence index wave) atTop (𝓝 (limit wave))) :
    Tendsto (fun index => quadraticFlux (complexSharpSupportProjection modes (sequence index))) atTop
      (𝓝 (quadraticFlux (complexSharpSupportProjection modes limit))) := by
  have projected (wave : IntegerWavevector) (coordinate : Coordinate) :
      Tendsto (fun index => complexSharpSupportProjection modes (sequence index) wave coordinate) atTop
        (𝓝 (complexSharpSupportProjection modes limit wave coordinate)) := by
    by_cases inside : wave ∈ modes
    · simpa only [complexSharpSupportProjection_apply, if_pos inside] using tendsto_pi_nhds.mp (rows wave) coordinate
    · simpa only [complexSharpSupportProjection_apply, if_neg inside, Pi.zero_apply] using tendsto_const_nhds (x := (0 : ℂ))
  apply tendsto_pi_nhds.mpr
  intro wave
  apply tendsto_pi_nhds.mpr
  intro output
  apply tendsto_pi_nhds.mpr
  intro input
  simp only [projected_flux_eq_finite]
  exact (tendsto_finsetSum modes (fun first _ => (projected first input).mul (projected (wave - first) output))).neg

def projectStress (modes : Finset IntegerWavevector) (stress : NativeFluidStressFourierState) : NativeFluidStressFourierState :=
  fun wave => if wave ∈ modes then stress wave else 0

def resolvedStress (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  projectStress modes (quadraticFlux velocity) - quadraticFlux (complexSharpSupportProjection modes velocity)

theorem resolvedStress_reads_original (modes : Finset IntegerWavevector) (vorticity : ComplexVorticityHilbertState) :
    resolvedStress modes (wholeBiotSavartVelocityState vorticity) = correctionStress modes vorticity := by
  funext wave output input
  simp only [resolvedStress, projectStress, correctionStress, NativeTurbulenceControl.velocity_projection, Pi.sub_apply]
  split_ifs <;> rfl

theorem resolvedAction_reads_original (modes : Finset IntegerWavevector) (vorticity : ComplexVorticityHilbertState)
    (zero : vorticity 0 = 0) (transverse : WholeStateTransverse vorticity) :
    nativeFluidConstitutiveVorticityAction (resolvedStress modes (wholeBiotSavartVelocityState vorticity)) =
      nativeTurbulenceCorrectionAt modes vorticity := by
  rw [resolvedStress_reads_original]
  funext wave
  exact correctionStress_action modes vorticity zero transverse wave

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def correctionLimit (stress : StressAt escape) (pointLe : point ≤ 1) (modes : Finset IntegerWavevector) :
    NativeFluidStressFourierState :=
  projectStress modes stress.stress -
    quadraticFlux (complexSharpSupportProjection modes (wholeVelocity (fixedEndpoint escape pointLe)))

theorem correction_stress_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (modes : Finset IntegerWavevector) :
    Tendsto (fun index => correctionStress modes (state escape (stress.refinement index))) atTop
      (𝓝 (correctionLimit stress pointLe modes)) := by
  have rows (wave) := (velocity_row_tendsto escape pointLe wave).comp stress.refinement_strict.tendsto_atTop
  simp only [← fixedEndpoint_reads_original escape pointLe] at rows
  have resolved := projected_flux_tendsto modes
    (fun index => wholeBiotSavartVelocityState (state escape (stress.refinement index)))
    (wholeVelocity (fixedEndpoint escape pointLe)) rows
  have filtered : Tendsto (fun index => projectStress modes (actualStress escape (stress.refinement index))) atTop
      (𝓝 (projectStress modes stress.stress)) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    by_cases inside : wave ∈ modes
    · simpa only [projectStress, if_pos inside] using tendsto_pi_nhds.mp stress.stress_tendsto wave
    · simpa only [projectStress, if_neg inside] using tendsto_const_nhds (x := (0 : NativeFluidStressCoefficient))
  have source := filtered.sub resolved
  have same (index) : projectStress modes (actualStress escape (stress.refinement index)) -
      quadraticFlux (complexSharpSupportProjection modes
        (wholeBiotSavartVelocityState (state escape (stress.refinement index)))) =
      correctionStress modes (state escape (stress.refinement index)) := by
    rw [actualStress_eq]
    exact resolvedStress_reads_original modes _
  simpa only [same, correctionLimit] using source

theorem correction_decomposition (stress : StressAt escape) (pointLe : point ≤ 1) (modes : Finset IntegerWavevector) :
    correctionLimit stress pointLe modes =
      resolvedStress modes (wholeVelocity (fixedEndpoint escape pointLe)) + projectStress modes (defect stress pointLe) := by
  funext wave output input
  simp only [correctionLimit, resolvedStress, projectStress, defect, Pi.add_apply, Pi.sub_apply]
  by_cases inside : wave ∈ modes <;> simp [inside]

theorem correction_action_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (modes : Finset IntegerWavevector) :
    Tendsto (fun index => nativeTurbulenceCorrectionAt modes (state escape (stress.refinement index))) atTop
      (𝓝 (nativeFluidConstitutiveVorticityAction
        (resolvedStress modes (wholeVelocity (fixedEndpoint escape pointLe))) +
          nativeFluidConstitutiveVorticityAction (projectStress modes (defect stress pointLe)))) := by
  have source := wholeStressActionCLM.continuous.tendsto (correctionLimit stress pointLe modes) |>.comp
    (correction_stress_tendsto stress pointLe modes)
  change Tendsto (fun index => nativeFluidConstitutiveVorticityAction
    (correctionStress modes (state escape (stress.refinement index)))) atTop
    (𝓝 (wholeStressActionCLM (correctionLimit stress pointLe modes))) at source
  have same (index) : nativeFluidConstitutiveVorticityAction (correctionStress modes (state escape (stress.refinement index))) =
      nativeTurbulenceCorrectionAt modes (state escape (stress.refinement index)) := by
    funext wave
    have physical := (ledger.family.stage (radius escape (stress.refinement index))).physical _
      (sampleTime escape pointLe (stress.refinement index)).2
    exact correctionStress_action modes _
      (physical.2.1 0 (zero_not_mem_puncturedIntegerWaveFrequencyCube _)) physical.2.2.1 wave
  simpa only [same, correction_decomposition, map_add, wholeStressActionCLM_apply] using source

theorem source_generated_joint_action_tendsto (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) (modes : Finset IntegerWavevector) :
    let escape := sourceUncoveredAction initial point inside uncovered
    let stress := sourceStress initial point inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    Tendsto (fun index =>
      (actualMomentum escape (stress.refinement index),
        (fun wave => sourcePressure (state escape (stress.refinement index)) wave),
        nativeTurbulenceCorrectionAt modes (state escape (stress.refinement index)))) atTop
      (𝓝 (resolvedMomentum escape pointLe + internalMomentum stress pointLe,
        (fun wave => stressPressureCoefficient wave (stress.stress wave)),
        nativeFluidConstitutiveVorticityAction (resolvedStress modes
          ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath ⟨point, inside.1.le, pointLe⟩)) +
          nativeFluidConstitutiveVorticityAction (projectStress modes (defect stress pointLe)))) := by
  dsimp only
  let escape := sourceUncoveredAction initial point inside uncovered
  let stress := sourceStress initial point inside uncovered
  have pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
  have momentum := momentum_tendsto stress pointLe
  rw [momentum_decomposition] at momentum
  have correction := correction_action_tendsto stress pointLe modes
  rw [fixedEndpoint_reads_original escape pointLe] at correction
  exact momentum.prodMk_nhds ((pressure_tendsto stress).prodMk_nhds correction)

end
end SaturationMonoid.NavierStokes.NativeRecoveryEscapeCorrection
