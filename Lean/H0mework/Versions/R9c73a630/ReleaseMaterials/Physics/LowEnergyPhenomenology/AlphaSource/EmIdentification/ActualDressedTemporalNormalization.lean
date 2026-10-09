import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointTemporal

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalNormalization
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical

/-- The original action generates all twelve temporal columns with the complete time weight. -/
theorem original_temporal_action (a : Fin 12) (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) :
    rawActionSymbol (temporalField a) p s=sourceTimeWeight s*chargeMatrix (originalUnit a) := by
  have coefficients : (fun i=>statePhase s*densityVariation (temporalField a) s i)=temporalCoefficient a :=
    funext (temporal_normalized_reader a s valid.1 valid.2)
  rw [rawActionSymbol_source _ p s valid,symbolFirst_field _ p s valid,coefficients]
  have fourier : fourierLinear p (temporalCoefficient a)=chargeMatrix (originalUnit a) :=
    temporal_full_matrix a p
  rw [fourier,sourceTimeWeight_original]
  simp only [mul_neg,smul_neg,neg_smul,smul_mul_assoc]
  module

/-- The original momentum inverse acts on both independent branches. -/
theorem canonical_temporal_action (a : Fin 12) (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) •
      rawActionSymbol (temporalField a) p s)=chargeMatrix (originalUnit a) := by
  rw [original_temporal_action a p s valid,←smul_mul_assoc,←mul_assoc,
    canonical_phase_time_weight s valid,one_mul]

/-- Full-Fock normalization retains the pair term in every Number sector. -/
theorem canonical_temporal_quantized (a : Fin 12) (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) :
    quantized (chargeMatrix (originalUnit a))=
      quantized (canonicalPhaseNormalizer s)*
          quantized ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (temporalField a) p s)-
        pairFiber (canonicalPhaseNormalizer s)
          ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (temporalField a) p s) := by
  have paid:=quantized_normal_order (canonicalPhaseNormalizer s)
    ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (temporalField a) p s)
  rw [canonical_temporal_action a p s valid] at paid
  exact eq_sub_of_add_eq paid.symm

end LowEnergy.GaussComposite.ActualDressedTemporalNormalization
