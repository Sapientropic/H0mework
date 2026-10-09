import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseHistory
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointOrbitCurrent

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
abbrev Operator:=H→L[ℂ] H
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity StageNineCoframeGravityGaugeRegularity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit
private def ambientGaugeLift : Gauge→ₗ[ℝ](Fin 4→NativeLie) :=
  LinearMap.pi (fun mu=>Fin.cases (0:Gauge→ₗ[ℝ]NativeLie)
    (fun j=>(LinearMap.proj j).comp gaugeCoordinates.toLinearMap) mu)

private def ambientData : Ambient→ₗ[ℝ]FieldData :=
  (LinearMap.fst ℝ Scalar Gauge).prod
    ((ambientGaugeLift.comp (LinearMap.snd ℝ Scalar Gauge)).prod 0)

/-- The original full scalar+spatial-gauge tangent uses the already generated original field-to-state map. -/
def phaseAmbientState : Ambient→ₗ[ℝ]ActionState := stateDirectionMap.comp ambientData

private theorem ambient_state_apply (v : Ambient) :
    phaseAmbientState v=(0,(fun mu=>Fin.cases 0 (fun j=>nativePrimal (gaugeCoordinates v.2 j)) mu),scalarLinear v.1) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    refine Fin.cases ?_ (fun j=>?_) mu
    · change spinLinear 0 0+nativePrimal 0=0
      rw [map_zero,map_zero,zero_add]
    · change spinLinear j.succ 0+nativePrimal (gaugeCoordinates v.2 j)=_
      rw [map_zero,zero_add]
      rfl
  · rfl

/-- This is the actual affine variation of the original full orbit, not a chosen slice vector. -/
def phaseAmbientDeviation (z : SourceCoordinateSlice) : Ambient :=
  variationL (z-GaussHistoryHilbert.sourcePoint.val) (sourcePhaseGaugeLie,0)

def phaseAmbientReference : Ambient := orbitMap GaussHistoryHilbert.sourcePoint.val sourcePhaseGaugeLie

private theorem phase_reference_state : sourceState GaussHistoryHilbert.sourcePoint.val=sourceReferenceState := by
  rw [←configurationState_emitter]
  change configurationState (emitter GaussHistoryHilbert.sourcePoint.val) 0=configurationState Stage9C.Material.SpinPair.actual 0
  apply Prod.ext
  · exact emitted_source_coframe
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (emitter GaussHistoryHilbert.sourcePoint.val) 0 mu)=_
    unfold FullQuantum.connection
    rw [emitted_source_gauge]
    rfl
  · exact congrArg scalarLinear emitted_source_scalar

theorem phase_slice_contact (h : SourceCoordinateSlice) :
    emGaugeState (sliceState h)=phaseAmbientState (variationL h (sourcePhaseGaugeLie,0)) := by
  rw [ambient_state_apply]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    refine Fin.cases ?_ (fun j=>?_) mu
    · change nativePrimal sourcePhaseGaugeLie*0-0*nativePrimal sourcePhaseGaugeLie=0
      rw [mul_zero,zero_mul,sub_zero]
    · change nativePrimal sourcePhaseGaugeLie*nativePrimal (SourceCartanCubic.gaugeCoordinate j (h.2.2:Gauge))-
        nativePrimal (SourceCartanCubic.gaugeCoordinate j (h.2.2:Gauge))*nativePrimal sourcePhaseGaugeLie=
      nativePrimal (jointP286CoordinateLieBracket sourcePhaseGaugeLie (gaugeCoordinates (h.2.2:Gauge) j))
      exact (originalGauge_commutator sourcePhaseGaugeLie (gaugeCoordinates (h.2.2:Gauge) j)).symm
  · exact (originalScalar_commutator sourcePhaseGaugeLie (h.2.1:Scalar)).symm

/-- The held-Ward configuration deviation is the restriction of this same generated ambient variation. -/
theorem phase_deviation_actual_state (z : SourceCoordinateSlice) :
    emOriginDeviationState (sourceState z)=phaseAmbientState (phaseAmbientDeviation z) := by
  have affine:=sourceState_affine GaussHistoryHilbert.sourcePoint.val (z-GaussHistoryHilbert.sourcePoint.val) 1
  have point : GaussHistoryHilbert.sourcePoint.val+(1:ℝ) • (z-GaussHistoryHilbert.sourcePoint.val)=z := by module
  rw [point,one_smul,phase_reference_state] at affine
  have same : sourceState z-sourceReferenceState=sliceState (z-GaussHistoryHilbert.sourcePoint.val) := by
    rw [affine]
    abel
  rw [emOriginDeviationState,same]
  exact phase_slice_contact _

theorem phase_deviation_ambient (z : SourceCoordinateSlice) :
    phaseAmbientDeviation z=orbitMap z sourcePhaseGaugeLie-phaseAmbientReference := by
  apply Prod.ext
  · change scalarP286ActionBilinear sourcePhaseGaugeLie ((z.2.1:Scalar)-(GaussHistoryHilbert.sourcePoint.val.2.1:Scalar))=
      scalarP286ActionBilinear sourcePhaseGaugeLie (vacuum+(z.2.1:Scalar))-
        scalarP286ActionBilinear sourcePhaseGaugeLie (vacuum+(GaussHistoryHilbert.sourcePoint.val.2.1:Scalar))
    rw [map_sub,map_add,map_add]
    abel
  · change nativeGauge sourcePhaseGaugeLie ((z.2.2:Gauge)-(GaussHistoryHilbert.sourcePoint.val.2.2:Gauge))=_
    exact (nativeGauge sourcePhaseGaugeLie).map_sub _ _

/-- Original inversion supplies the complete Lie component and zero slice component of the full orbit. -/
theorem phase_orbit_inverse (z : physicalChart) :
    inverseL z.val (orbitMap z.val sourcePhaseGaugeLie)=(sourcePhaseGaugeLie,0) := by
  have same : orbitMap z.val sourcePhaseGaugeLie=splitMap z.val (sourcePhaseGaugeLie,0) := by
    simp [splitMap,sliceMap]
  rw [same,inverse_left]

/-- The emitted deviation retains its real configuration direction and its matching native connection. -/
theorem phase_deviation_inverse (z : physicalChart) :
    inverseL z.val (phaseAmbientDeviation z.val)=
      (sourcePhaseGaugeLie,0)-inverseL z.val phaseAmbientReference := by
  rw [phase_deviation_ambient,map_sub,phase_orbit_inverse]

/-- Arbitrary original full289 forcing keeps the exact chart/fiber complement in the actual moving phase contact. -/
theorem phase_deviation_field_contact (force : Field289) (z : SourceCoordinateSlice) :
    emGaugeState (fieldDirection force)=
      phaseAmbientState (variationL (PreparationVacuumFieldConstraintResponse.fieldVector force z) (sourcePhaseGaugeLie,0))+
        emGaugeState (complement force z) := by
  have split : fieldDirection force=sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z)+complement force z := by
    rw [complement]
    abel
  have generated:=congrArg emGaugeState split
  rw [map_add,phase_slice_contact] at generated
  exact generated

/-- The literal nonzero scalar orbit cannot be installed as a tangent of the fixed 61-dimensional scalar slice. -/
theorem phase_scalar_outside_slice : orbit sourcePhaseGaugeLie∉scalarSlice := by
  have nonzero : orbit sourcePhaseGaugeLie≠0:=em_orbit_scalar_nonzero
  intro inside
  have perpendicular:=(Submodule.mem_orthogonal _ _).1 inside (orbit sourcePhaseGaugeLie) ⟨sourcePhaseGaugeLie,rfl⟩
  exact nonzero ((inner_self_eq_zero (𝕜:=ℝ)).mp perpendicular)

end LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
