import H0mework.NavierStokes.RecoveryAction.RecoveryNonlinear
import H0mework.NavierStokes.TimeJets.TimeRecursion
import H0mework.NavierStokes.VelocityEndpoint.MacroCausalDuhamel
import H0mework.NavierStokes.ShellSources.WholeReceiptSquareContinuation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryRowAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointMacroCausalDuhamel
open NativeRecoveryNonlinear NativeStressSource NativeTimeJetCarrier NativeHigherTimeJets

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

def velocity (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (actual : ℝ) : ComplexVorticityHilbertState := receipt.wholePath (projIcc (0 : ℝ) 1 zero_le_one actual)

theorem velocity_on_interval (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : velocity receipt time.1 = receipt.wholePath time := by
  unfold velocity
  rw [projIcc_of_mem zero_le_one time.2]

def nonlinearRow (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (quadraticFlux (velocity receipt actual) wave)

def rateRow (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  nonlinearRow receipt wave actual - (nu.coeff * integerWaveViscousMultiplier wave) • velocity receipt actual wave

def inheritedForcing (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension 1 (wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave))

def rowExtension (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath (wholeRestartVelocityEndpointCoefficient ledger.family.endpointReceipt.velocityEndpoint wave)
    (inheritedForcing receipt wave) (nu.coeff * integerWaveViscousMultiplier wave) 0

theorem rowExtension_on_interval (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) 1) :
    rowExtension receipt wave time.1 = velocity receipt time.1 wave := by
  rw [velocity_on_interval, receipt.row_mild_identity wave nonzero time,
    fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath 1 zero_le_one]
  rfl

theorem inheritedForcing_integrable (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : IntervalIntegrable (inheritedForcing receipt wave) volume 0 1 :=
  commonTimeZeroExtension_intervalIntegrable 1 zero_le_one _

theorem inheritedForcing_eq_source_ae (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : ∀ᵐ time : ℝ, time ∈ Icc (0 : ℝ) 1 →
      inheritedForcing receipt wave time = nonlinearRow receipt wave time := by
  have common : commonTimeMeasure 1 = Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  apply (ae_restrict_iff' measurableSet_Icc).mp
  rw [ae_restrict_iff_subtype measurableSet_Icc, ← common]
  filter_upwards [wholeMild_lerayLimit_eq_flux receipt wave] with time same
  rw [inheritedForcing, commonTimeZeroExtension_of_mem 1 _ time.1 time.2,
    nonlinearRow, velocity_on_interval]
  exact same

theorem rowExtension_absolutelyContinuous (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : AbsolutelyContinuousOnInterval (rowExtension receipt wave) 0 1 :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval _ _ _
    (inheritedForcing_integrable receipt wave) (by simp)

theorem rowExtension_derivative_ae (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) : ∀ᵐ time : ℝ, time ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (rowExtension receipt wave) (rateRow receipt wave time) time := by
  have derivative := heatDuhamelComplexCoordinatePath_ae_hasDerivAt
    (wholeRestartVelocityEndpointCoefficient ledger.family.endpointReceipt.velocityEndpoint wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0 (inheritedForcing_integrable receipt wave) (by simp)
  filter_upwards [derivative, inheritedForcing_eq_source_ae receipt wave] with time evolves forcingSame
  intro inside
  have actual := evolves (by simpa only [uIcc_of_le zero_le_one] using inside)
  change HasDerivAt (rowExtension receipt wave)
    (inheritedForcing receipt wave time - (nu.coeff * integerWaveViscousMultiplier wave) • rowExtension receipt wave time) time at actual
  rw [forcingSame inside, rowExtension_on_interval receipt wave nonzero ⟨time, inside⟩] at actual
  exact actual

theorem rateRow_continuousOn (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (domain : Set ℝ) (continuous : ContinuousOn (velocity receipt) domain) (wave : IntegerWavevector) :
    ContinuousOn (rateRow receipt wave) domain := by
  have tensor : ContinuousOn (fun actual => quadraticFlux (velocity receipt actual) wave) domain := by
    apply continuousOn_pi.mpr
    intro output
    apply continuousOn_pi.mpr
    intro input
    exact ((mixedFluxCLM wave output input).continuous.comp_continuousOn continuous).clm_apply continuous
  exact ((projectedDivergenceCLM wave).continuous.comp_continuousOn tensor).sub
    (((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp_continuousOn
      continuous).const_smul (nu.coeff * integerWaveViscousMultiplier wave))

theorem hasDerivWithinAt_of_source_integral (path tangent : ℝ → ComplexCoordinateVector)
    (left right : ℝ) (ordered : left ≤ right)
    (pathAC : AbsolutelyContinuousOnInterval path left right)
    (tangentContinuous : ContinuousOn tangent (Icc left right))
    (derivative : ∀ᵐ time : ℝ, time ∈ Icc left right → HasDerivAt path (tangent time) time)
    (time : ℝ) (inside : time ∈ Icc left right) :
    HasDerivWithinAt path (tangent time) (Icc left right) time := by
  let extended (actual : ℝ) := tangent (projIcc left right ordered actual).1
  have extendedContinuous : Continuous extended := tangentContinuous.domRestrict.comp continuous_projIcc
  have same (actual : ℝ) (member : actual ∈ Icc left right) : extended actual = tangent actual := by
    simp only [extended, projIcc_of_mem ordered member]
  have tangentIntegrable := tangentContinuous.intervalIntegrable_of_Icc (μ := volume) ordered
  have sourceAE : ∀ᵐ actual : ℝ, actual ∈ uIcc left right → HasDerivAt path (tangent actual) actual := by
    simpa only [uIcc_of_le ordered] using derivative
  have integralSame (actual : ℝ) (member : actual ∈ Icc left right) :
      (∫ sample in left..actual, extended sample) = ∫ sample in left..actual, tangent sample := by
    apply intervalIntegral.integral_congr
    intro sample sampleInside
    exact same sample (by
      rw [uIcc_of_le member.1] at sampleInside
      exact ⟨sampleInside.1, sampleInside.2.trans member.2⟩)
  have actual := (intervalIntegral.integral_hasDerivAt_right
    (extendedContinuous.intervalIntegrable left time)
    extendedContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    extendedContinuous.continuousAt).const_add (path left)
  rw [same time inside] at actual
  apply actual.hasDerivWithinAt.congr_of_mem _ inside
  intro sample member
  rw [integralSame sample member, ← path_sub_eq_intervalIntegral pathAC tangentIntegrable sourceAE sample
    (by simpa only [uIcc_of_le ordered] using member)]
  abel

theorem hilbert_hasDerivWithinAt_on_interval (field rate : ℝ → ComplexVorticityHilbertState)
    (left right : ℝ) (ordered : left ≤ right)
    (fieldContinuous : ContinuousOn field (Icc left right))
    (rateContinuous : ContinuousOn rate (Icc left right))
    (rows : ∀ wave time, time ∈ Icc left right →
      HasDerivWithinAt (fun actual => field actual wave) (rate time wave) (Icc left right) time)
    (time : ℝ) (inside : time ∈ Icc left right) :
    HasDerivWithinAt field (rate time) (Icc left right) time := by
  let shifted (curve : ℝ → ComplexVorticityHilbertState) (actual : ℝ) :=
    curve (projIcc left right ordered (left + actual)).1
  have continuousShift (curve : ℝ → ComplexVorticityHilbertState) (continuous : ContinuousOn curve (Icc left right)) :
      Continuous (shifted curve) :=
    (continuous.domRestrict.comp continuous_projIcc).comp (continuous_const.add continuous_id)
  have maps : MapsTo (fun actual : ℝ => left + actual) (Icc (0 : ℝ) (right - left)) (Icc left right) := by
    intro actual member
    constructor <;> linarith [member.1, member.2]
  have same (curve : ℝ → ComplexVorticityHilbertState) (actual : ℝ) (member : actual ∈ Icc (0 : ℝ) (right - left)) :
      shifted curve actual = curve (left + actual) := by
    simp only [shifted, projIcc_of_mem ordered (maps member)]
  have base := NativeTimeJetRecursion.hilbert_hasDerivWithinAt_of_rows (right - left)
    (shifted field) (shifted rate) (continuousShift field fieldContinuous) (continuousShift rate rateContinuous)
    (fun wave sample member => by
      have shift : HasDerivWithinAt (fun actual : ℝ => left + actual) 1 (Icc (0 : ℝ) (right - left)) sample := by
        simpa using ((hasDerivAt_id sample).const_add left).hasDerivWithinAt
      have derived := (rows wave (left + sample) (maps member)).scomp sample shift maps
      simp only [one_smul] at derived
      rw [same rate sample member]
      exact derived.congr_of_mem
        (fun actual actualInside => congrArg (fun state : ComplexVorticityHilbertState => state wave)
          (same field actual actualInside)) member)
    ⟨time - left, by constructor <;> linarith [inside.1, inside.2]⟩
  have point : time - left ∈ Icc (0 : ℝ) (right - left) := by
    constructor <;> linarith [inside.1, inside.2]
  rw [same rate (time - left) point, add_sub_cancel] at base
  have unshift : HasDerivWithinAt (fun actual : ℝ => actual - left) 1 (Icc left right) time := by
    simpa using ((hasDerivAt_id time).sub_const left).hasDerivWithinAt
  have returns : MapsTo (fun actual : ℝ => actual - left) (Icc left right) (Icc (0 : ℝ) (right - left)) := by
    intro actual member
    constructor <;> linarith [member.1, member.2]
  have actual := base.scomp time unshift returns
  simp only [one_smul] at actual
  apply actual.congr_of_mem _ inside
  intro sample member
  change field sample = shifted field (sample - left)
  rw [same field (sample - left) (returns member), add_sub_cancel]

end
end SaturationMonoid.NavierStokes.NativeRecoveryRowAction
