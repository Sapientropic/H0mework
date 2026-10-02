import H0mework.Versions.R2.Physics.SourceFormation.Consumer
import H0mework.Versions.R2.Physics.SourceFormation.Qualification

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCClassicalWorldAcceptance
open StageNineConnectionSectorSourceBalance StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineLorentzConnectionVariation
open SU7MotherLieAlgebra

noncomputable section

theorem matter_current_eq (source : SmoothUnifiedSource) (point : BasePoint) (variation : P286GaugeOneForm) :
    p286MatterCurrentCoefficient source (formedField source) variation point =
      p286MatterCurrentCoefficient (SourceFamily.sourceAt (index source))
        (SourceFamily.fieldAt (index source)) variation point := by
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum holonomicMatterGaugeConnectionVariation
    generatedVolumeDensity
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    toContinuumPointField, coframe_eq, matter_eq, dual_eq]

theorem matter_spin_eq (source : SmoothUnifiedSource) (point : BasePoint) (variation : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient source (formedField source) variation point =
      lorentzMatterSpinSourceCoefficient (SourceFamily.sourceAt (index source))
        (SourceFamily.fieldAt (index source)) variation point := by
  unfold lorentzMatterSpinSourceCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum holonomicMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    toContinuumPointField, coframe_eq, matter_eq, dual_eq]

theorem matter_current_nonzero (source : SmoothUnifiedSource) (point : BasePoint) :
    MatterCurrentNonzeroAt source (formedField source) point := by
  obtain ⟨variation, nonzero⟩ := SourceFamily.Qualification.matter_current_nonzero (index source) point
  refine ⟨variation, ?_⟩
  rw [matter_current_eq]
  exact nonzero

theorem matter_spin_nonzero (source : SmoothUnifiedSource) (point : BasePoint) :
    MatterSpinNonzeroAt source (formedField source) point := by
  obtain ⟨variation, nonzero⟩ := SourceFamily.Qualification.matter_spin_nonzero (index source) point
  refine ⟨variation, ?_⟩
  rw [matter_spin_eq]
  exact nonzero

/-- The original six-sector key applies exactly when its two vacuum-owned
nonzero sectors are present. Every raw source already has the full Euler realization. -/
theorem material_acceptance_iff (source : SmoothUnifiedSource) :
    ClassicalWorldAcceptance source (MotherFamilyOccurrence.materialField source) ↔
      source.stageEight.physicalPhaseAmplitude ≠ 0 := by
  rw [← material_field_eq]
  constructor
  · intro acceptance
    exact (Qualification.vacuum_nonzero_iff source).mp
      acceptance.simultaneousSixPhysicalSectorNonzero.breakingVacuum
  · intro amplitude
    refine
      { smooth := field_smooth source
        nondegenerate := field_nondegenerate source
        gravityConnectionLorentzAdmissible := lorentz_admissible source
        jointZeroFiber := joint_zero source
        dynamicScalarSourceContact := ?_
        simultaneousSixPhysicalSectorNonzero := ?_ }
    · rw [material_field_eq]
      exact (material_realization source).2.2.2.2
    · refine
        { gravityCurvature := ?_
          p286GaugeCurvature := ?_
          breakingVacuum := (Qualification.vacuum_nonzero_iff source).2 amplitude
          yukawaMass := (Qualification.mass_nonzero_iff source).2 amplitude
          matterCurrent := ⟨0, matter_current_nonzero source 0⟩
          stressOrSpin := ⟨0, Or.inr (matter_spin_nonzero source 0)⟩ }
      · refine ⟨0, ?_⟩
        rw [gravity_curvature_eq]
        exact SourceFamily.Qualification.gravity_curvature_nonzero (index source) 0
      · refine ⟨0, ?_⟩
        rw [gauge_curvature_eq]
        exact SourceFamily.field_curvature_nonzero (index source) 0

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation
