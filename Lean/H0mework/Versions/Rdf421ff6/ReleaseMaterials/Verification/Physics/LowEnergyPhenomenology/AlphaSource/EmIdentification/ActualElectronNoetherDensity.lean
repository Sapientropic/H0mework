import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCoulombCoefficient
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeOriginWard
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronNoetherDensity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDensityCore GaussHistoryHilbert
open PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationVacuumSourceFieldFamily PreparationPhysicalActionUnits
open PreparationVacuumFullFieldRiesz
open PreparationVacuumOriginalDensity PreparationVacuumNonlinearFieldCurve PreparationVacuumActualFieldQuantization
open PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualCompositeOriginWard
open ActualDressedNoetherCoulombUnit ActualDressedActionPhase ActualDressedTemporalForm
open PhysicalEMGaugeRealization PhysicalEMVoltage PreparationPhysicalSignedVolumeWeightReturn
open PreparationVacuumWeightedChargeActionWard PreparationPhysicalFirstTemporalChargeReturn
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local irreducible] sourceState sourceTimeWeight sourceWeightSymbol rawActionSymbol
  compositeUnitLeg compositeChargeCore sourcePair noetherEMCurrent

/-- The actual source temporal momentum retains the full signed independent-dual matrix and local coframe volume. -/
theorem actual_em_time_weight (z : physicalChart) :
    sourceTimeWeight (sourceState z.val)=
      ((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z.val : ℝ) : ℂ) • sourceTimeSignMatrix := by
  calc
    _=sourceWeightSymbol z.val := by
      unfold sourceWeightSymbol
      exact sourceTimeWeight_original (sourceState z.val)
    _=_ := sourceWeightSymbol_signed z

/-- This is the actual raw EM action density on arbitrary complete source tests, before a scalar h division. -/
theorem actual_em_signed_density_sample (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    rawSample (emGaugeField 0) p a b (0,z)=sourceSignedVolumeSample emGaugeChargeMatrix a b z := by
  by_cases inside : z∈tsupport a
  · have valid : sourceState z∈validStates :=
      PreparationVacuumNonlinearFieldCurve.sourceState_valid ⟨z,a.tsupport_subset inside⟩
    unfold rawSample rawFiber sourceSignedVolumeSample
    rw [ambientState_zero,original_em_noether_symbol p (sourceState z) valid,
      actual_em_time_weight ⟨z,a.tsupport_subset inside⟩,smul_mul_assoc,map_smul,smul_apply,pairSample_smul_right]
  · rw [rawSample_zero _ p a b 0 z inside]
    simp only [sourceSignedVolumeSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,mul_zero]

/-- The original full field integral is exactly the same source signed-volume charge form. -/
theorem actual_em_signed_density_form (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm (emGaugeField 0) p a b 0=sourceSignedVolumeForm emGaugeChargeMatrix a b := by
  unfold rawForm sourceSignedVolumeForm
  exact integral_congr_ae (Eventually.of_forall (actual_em_signed_density_sample p a b))

/-- Momentum-independent temporal charge is read from the actual coframe/independent-dual density, not inferred from input charge labels. -/
theorem actual_noether_signed_density_read (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherEMCurrent p left right 0=
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹*
        sourcePair (compositeUnitLeg left)
          (sourceTemporalMatrixCore emGaugeChargeMatrix (compositeUnitLeg right)) := by
  rw [actual_noether_em_reader p left right 0,actual_em_signed_density_form,
    sourceSignedVolumeForm_actual]

/-- The actual zero-momentum Noether charge is the same raw action reader for every original Fourier momentum. -/
theorem actual_noether_zero_momentum_read (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherEMCurrent p left right 0=noetherEMCurrent 0 left right 0 := by
  rw [actual_noether_signed_density_read p left right,actual_noether_signed_density_read 0 left right]

/-- Full canonical temporal normalization keeps the original CAR pair correction before reading the actual propagated endpoints. -/
theorem actual_canonical_em_action_charge (p : PhysicalMomentum) (left right : CompositeLeg) :
    emActionForm p (compositeUnitLeg left) (compositeUnitLeg right)=actualChargeRead left right := by
  rw [em_action_form,←composite_charge_original]
  rfl

/-- The h-normalized raw reader's calibration is a generated source vector containing its real signed-volume density difference. -/
def actualDensityCorrection (right : CompositeLeg) : QuantumTest :=
  (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
    sourceTemporalMatrixCore emGaugeChargeMatrix (compositeUnitLeg right)-
      compositeChargeCore (compositeUnitLeg right)

/-- The entire density defect has a concrete source coframe/time/dual realization on the same full output. -/
theorem actual_noether_density_correction (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherDensityDefect p left right=sourcePair (compositeUnitLeg left) (actualDensityCorrection right) := by
  have original := actual_noether_density_return p left right
  rw [actual_noether_signed_density_read p left right] at original
  have pair : sourcePair (compositeUnitLeg left) (actualDensityCorrection right)=
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹*
        sourcePair (compositeUnitLeg left) (sourceTemporalMatrixCore emGaugeChargeMatrix (compositeUnitLeg right))-
          actualChargeRead left right := by
    simp only [actualDensityCorrection,sourcePair,actualChargeRead,map_sub,map_smul,inner_sub_right,inner_smul_right]
  rw [pair]
  exact eq_sub_of_add_eq' original.symm

end LowEnergy.GaussComposite.ActualElectronNoetherDensity
