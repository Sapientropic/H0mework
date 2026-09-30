import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.Versions.X.NavierStokes.FullOrder.RecoveryTimeGramWrite

/-! Full stress rates and Bochner work from the original physical stages.
Their pairings retain the same moving-anchor and fixed-time source work. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRawStressAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeRecoveryTimeGramAction NativeCompleteStressBilinear NativeCompleteStressCarrier
open NativeEndpointVelocityCarrier NativeCofinalStressPositivity

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stage (stress : StressAt escape) (index : ℕ) :=
  ledger.family.stage (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index))

def rawField (stress : StressAt escape) (index : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  biotSavartCLM ((stage stress index).trajectory time)

def rawRate (stress : StressAt escape) (index : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  biotSavartCLM (finiteStateVorticityGenerator
    (wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index)))
    nu.coeff ((stage stress index).trajectory time))

theorem rawField_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) : HasDerivAt (rawField stress index) (rawRate stress index time) time :=
  biotSavartCLM.hasFDerivAt.comp_hasDerivAt time ((stage stress index).physical time inside).1

def rawStress (stress : StressAt escape) (index : ℕ) (time : ℝ) : NativeCompleteStressCarrier.Space :=
  mixed (rawField stress index time) (rawField stress index time)

def rawStressRate (stress : StressAt escape) (index : ℕ) (time : ℝ) : NativeCompleteStressCarrier.Space :=
  mixed (rawRate stress index time) (rawField stress index time) +
    mixed (rawField stress index time) (rawRate stress index time)

theorem rawStress_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) : HasDerivAt (rawStress stress index) (rawStressRate stress index time) time := by
  have derivative := rawField_hasDerivAt stress index time inside
  exact (mixedCLM.hasFDerivAt.comp_hasDerivAt time derivative).clm_apply derivative

theorem rawRate_continuousOn (stress : StressAt escape) (index : ℕ) :
    ContinuousOn (rawRate stress index) (Icc (0 : ℝ) 1) := by
  have path : ContinuousOn (stage stress index).trajectory (Icc (0 : ℝ) 1) :=
    fun time inside => ((stage stress index).physical time inside).1.continuousAt.continuousWithinAt
  exact biotSavartCLM.continuous.comp_continuousOn
    ((finiteStateVorticityGenerator_contDiff _ nu.coeff).continuous.comp_continuousOn path)

theorem rawStressRate_continuousOn (stress : StressAt escape) (index : ℕ) :
    ContinuousOn (rawStressRate stress index) (Icc (0 : ℝ) 1) := by
  have field : ContinuousOn (rawField stress index) (Icc (0 : ℝ) 1) :=
    fun time inside => (rawField_hasDerivAt stress index time inside).continuousAt.continuousWithinAt
  exact ((mixedCLM.continuous.comp_continuousOn (rawRate_continuousOn stress index)).clm_apply field).add
    ((mixedCLM.continuous.comp_continuousOn field).clm_apply (rawRate_continuousOn stress index))

theorem rawStress_integral (stress : StressAt escape) (index : ℕ) (first last : Icc (0 : ℝ) 1) :
    (∫ time in first.1..last.1, rawStressRate stress index time) =
      rawStress stress index last.1 - rawStress stress index first.1 := by
  have subset : uIcc first.1 last.1 ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc first.2 last.2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => rawStress_hasDerivAt stress index time (subset inside))
    ((rawStressRate_continuousOn stress index).mono subset).intervalIntegrable

theorem rawField_node (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    rawField stress index (timeAt escape pointLe (stress.refinement index) node).1 =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) := by
  rw [rawField, biotSavartCLM_apply]
  unfold NativeRecoveryTimeGramRaw.velocity
  rw [wholeVelocity_punctured]
  rfl

theorem rawStress_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) (wave : IntegerWavevector) (output input : Coordinate) :
    read (rawStress stress index time) wave output input =
      -inner ℂ (field escape (stress.refinement index) wave output time)
        (field escape (stress.refinement index) 0 input time) := by
  have same := rawField_node stress pointLe index (.fixed ⟨time, inside⟩)
  change rawField stress index time = _ at same
  have left := field_read escape pointLe (stress.refinement index) (.fixed ⟨time, inside⟩) wave output
  have right := field_read escape pointLe (stress.refinement index) (.fixed ⟨time, inside⟩) 0 input
  simp only [timeAt] at left right
  rw [rawStress, mixed_read, NativeHigherTimeJets.mixedFlux_diagonal, same]
  rw [left, right]
  change _ = -inner ℂ (shiftedComponent _ (wave, output)) (shiftedComponent _ (0, input))
  rw [shiftedComponent_inner _ (velocity_reality escape pointLe (stress.refinement index) (.fixed ⟨time, inside⟩)),
    NativeCofinalFluxPairing.bilinearFlux_diagonal, sub_zero, neg_neg]

theorem rawStressRate_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) (wave : IntegerWavevector) (output input : Coordinate) :
    read (rawStressRate stress index time) wave output input =
      -pairedPower escape (stress.refinement index) (wave, output) (0, input) time := by
  have lhs := (readCLM wave output input).hasFDerivAt.comp_hasDerivAt time
    (rawStress_hasDerivAt stress index time inside)
  have rhs := ((field_hasDerivAt escape (stress.refinement index) wave output time inside).inner ℂ
    (field_hasDerivAt escape (stress.refinement index) 0 input time inside)).neg
  have matched := rhs.hasDerivWithinAt.congr_of_mem
    (fun sample member => rawStress_pairing stress pointLe index sample member wave output input) inside
  exact (lhs.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside)).symm.trans
    (matched.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside))

def rawWork (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (first last : TimeNode) :
    NativeCompleteStressCarrier.Space :=
  ∫ time in (timeAt escape pointLe (stress.refinement index) first).1..
    (timeAt escape pointLe (stress.refinement index) last).1, rawStressRate stress index time

theorem rawWork_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (first last : TimeNode) :
    rawWork stress pointLe index first last =
      rawStress stress index (timeAt escape pointLe (stress.refinement index) last).1 -
        rawStress stress index (timeAt escape pointLe (stress.refinement index) first).1 :=
  rawStress_integral stress index _ _

theorem rawWork_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) (output input : Coordinate) :
    read (rawWork stress pointLe index first last) wave output input =
      -pairedWork escape pointLe (stress.refinement index) first last (wave, output) (0, input) := by
  rw [rawWork_eq]
  change (readCLM wave output input) (_ - _) = _
  rw [map_sub, readCLM_apply, readCLM_apply,
    rawStress_pairing stress pointLe index _ (timeAt escape pointLe (stress.refinement index) last).2,
    rawStress_pairing stress pointLe index _ (timeAt escape pointLe (stress.refinement index) first).2,
    pairedWork_eq, field_read, field_read, field_read, field_read]
  abel

theorem source_stress_work (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => read (rawWork stress pointLe index first last) wave output input)
      ((NativeRecoveryJointTimeKernel.generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (NativeRecoveryTimeGramReadout.stressRead stress pointLe last wave output input -
        NativeRecoveryTimeGramReadout.stressRead stress pointLe first wave output input)) := by
  simpa only [rawWork_pairing] using source_stress_write stress pointLe first last wave output input

end
end SaturationMonoid.NavierStokes.NativeRawStressAction
