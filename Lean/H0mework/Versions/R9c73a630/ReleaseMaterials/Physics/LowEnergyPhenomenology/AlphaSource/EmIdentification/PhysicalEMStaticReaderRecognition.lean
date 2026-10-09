import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticCompositeCurrent
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawJointReaderCompression

/-! Actual reader recognition: the complete `currentRestriction` of
`sourceStaticCompositeGauge` splits into the raw gauge-slot mode reader
`rawForm(gaugeField 1 0) - rawForm(gaugeField 2 1)` plus an explicit
compensation carrying the retained native/coframe/matter/fiber source
sectors. No `D_actual`/`w_J` target is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open PreparationPhysicalStaticCompositeProjectionReturn PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace

attribute [local irreducible] currentVertex CanonicalPhysicalYResolvent.finiteFull
  frameVector frameTest rawForm nativeFieldJets coframeFieldJets fiberFieldJets fieldJets

/-- The raw gauge-slot mode form: original `gaugeField 1 0` minus
`gaugeField 2 1` raw forms at the zero local gauge slice. -/
def emStaticReaderModeForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  rawForm (gaugeField 1 0) p a b 0-rawForm (gaugeField 2 1) p a b 0

/-- The compensation configuration retains every surviving source sector:
native first jet, coframe first jet, the density/matter integral and the
retained fiber `Y`-term, minus the raw slot forms. -/
def emStaticReaderCompensationConfiguration (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  (nativeFieldJets sourceStaticCompositeGauge a b).first 0+
    (coframeFieldJets sourceStaticCompositeGauge a b).first 0+
    (∫z,sourceStaticCompositeMatter p a b z ∂GaussHistoryHilbert.configurationMeasure)-
    rawForm (gaugeField 1 0) p a b 0+
    rawForm (gaugeField 2 1) p a b 0-
    (fiberFieldJets sourceStaticCompositeGauge retainedCoefficient retainedCoefficient_smooth a b).first 0

/-- The complete `fieldJets` first jet of the composite gauge field is the
raw mode form plus the retained source compensation, pointwise on tests. -/
theorem em_static_reader_field_generated (p : PhysicalMomentum) (a b : QuantumTest) :
    (fieldJets sourceStaticCompositeGauge p a b).first 0=
      emStaticReaderModeForm p a b+emStaticReaderCompensationConfiguration p a b := by
  rw [sourceStaticCompositeConfiguration_generated]
  unfold emStaticReaderCompensationConfiguration emStaticReaderModeForm
    sourceStaticCompositeConfiguration
  ring

/-- The raw mode reader on the original frame. -/
def emStaticReaderModeReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  rawReader (gaugeField 1 0) p F 0-rawReader (gaugeField 2 1) p F 0

/-- The retained compensation as an operator on the original frame. -/
def emStaticReaderCompensation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>emStaticReaderCompensationConfiguration p (frameTest F i) (frameTest F j))

/-- The raw reader difference is the `finiteRiesz` of the mode form by
literal rankOne linearity. -/
theorem em_static_modeReader_finiteRiesz (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    emStaticReaderModeReader p F=
      finiteRiesz F (fun i j=>emStaticReaderModeForm p (frameTest F i) (frameTest F j)) := by
  unfold emStaticReaderModeReader rawReader emStaticReaderModeForm finiteRiesz
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (sub_smul _ _ _).symm

/-- The complete `currentRestriction` of the composite gauge field on the
original frame splits into the raw mode reader plus the retained
compensation operator. -/
theorem em_static_reader_currentRestriction_generated (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    currentRestriction sourceStaticCompositeGauge p F 0=
      emStaticReaderModeReader p F+emStaticReaderCompensation p F := by
  rw [em_static_modeReader_finiteRiesz]
  unfold currentRestriction emStaticReaderCompensation finiteRiesz
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (congrArg (·•InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
    (em_static_reader_field_generated p (frameTest F i) (frameTest F j))).trans
      (add_smul _ _ _)

/-- The complete prepared gauge vertex contracts to the full retained
configuration on arbitrary `x`/`y`, keeping `fullY57` and `cut`. -/
theorem em_static_reader_currentVertex_pair (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    inner ℂ x (currentVertex sourceStaticCompositeGauge p k F cut z w y)=
      sourceStaticCompositeConfiguration p
        (sourceTestApprox F ((CanonicalPhysicalYResolvent.finiteFull (p+k) F cut z).adjoint x))
        (sourceTestApprox F (CanonicalPhysicalYResolvent.finiteFull p F cut w y)) := by
  rw [currentVertex_original_pair]
  exact sourceStaticCompositeConfiguration_generated p _ _

end LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition
