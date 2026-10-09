import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseNonlinearCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMNativeChargeFull
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.PreparedCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationActionBoundary

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintEndpoint
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert GaussDensityCore
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
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
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit

open PreparationVacuumFieldConstraintResponse SourceGraph
open ActualDressedPhaseWard ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
open PreparationVacuumElectricConstraint PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open CanonicalGradedCharge GaussFockPair PreparationVacuumSourcePreparedResponse
attribute [local irreducible] sourceState sourceSymbol sourceActionWeight phaseHeldAction phaseHeldMixed
  sourceReferenceState sourceDressedUnit sourceProfile jointResolvent chargeReader dressedEulerObserver prepared


open ActualDressedPhaseConfiguration ActualDressedNonlinearHalf


open PhysicalEMNativeChargeFull PhysicalEMGaugeRealization
open Stage9DEF Stage9DEF.Compatibility Stage10.ChargedPreparation.CanonicalParticle
open DiracExteriorMatterAction StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open CanonicalCompletedSector CanonicalPreparationCreation ActualDressedPreparationEnergy
open PreparationPhysicalJointEMCouplingUnitReturn
attribute [local instance] SourceRealScalarFock.branchOrder

def phaseColorProjection (v : Stage9DEF.Source.Index→ℂ) : Stage9DEF.Source.Index→ℂ :=
  fun i=>if i.2=0 then v i else 0

def phasePrimalPacket (v : Stage9DEF.Source.Index→ℂ) : Mode→ℂ :=
  Sum.elim (Quantum.coordinates (Stage9DEF.Compatibility.embed v)) (fun _=>0)

private theorem spinor_negative (A : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (-A)= -exteriorSpinorMotherLieAction A := by
  rw [show -A=(-1:ℝ) • A from (neg_one_smul ℝ A).symm,
    StageNineP286GaugeConnectionVariation.exteriorSpinorMotherLieAction_real_smul]
  push_cast
  module

private theorem phase_doublet (c : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed emDirection) (sourceColorDoubletMatter c)=
      if c=0 then (-Complex.I) • sourceColorDoubletMatter c else 0 := by
  rw [emDirection,sub_eq_add_neg,p286LieBlockEmbed_add,p286LieBlockEmbed_neg,
    p286LieBlockEmbed_neg,p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.exteriorSpinorMotherLieAction_add]
  rw [spinor_negative,spinor_negative,
    StageNineP286GaugeConnectionVariation.exteriorSpinorMotherLieAction_real_smul]
  simp only [LinearMap.add_apply,LinearMap.neg_apply,LinearMap.smul_apply,
    sourceColorDoublet_generatorAction,source_doublet_charge]
  fin_cases c <;> simp [sourceColorPauli,Fin.sum_univ_two,smul_smul]
  all_goals module

/-- The literal original phase action, evaluated on the actual color-doublet carrier before any quantum completion. -/
theorem phase_embedding_generated (v : Stage9DEF.Source.Index→ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm sourcePhaseGaugeLie))
      (Stage9DEF.Compatibility.embed v)=
      (-Complex.I) • Stage9DEF.Compatibility.embed (phaseColorProjection v) := by
  rw [phase_lie_original]
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed emDirection)
    (∑c : Fin 2,v (spin,c) • sourceColorDoubletMatter c)=_
  rw [map_sum]
  simp only [map_smul,phase_doublet]
  change (∑c : Fin 2,v (spin,c) • (if c=0 then (-Complex.I) • sourceColorDoubletMatter c else 0))=
    (-Complex.I) • (∑c : Fin 2,phaseColorProjection v (spin,c) • sourceColorDoubletMatter c)
  have different : (1:Fin 2)≠0 := by decide
  simp only [Fin.sum_univ_two,phaseColorProjection,if_pos rfl,if_neg different,smul_zero,add_zero,zero_smul]
  exact smul_comm _ _ _

/-- All504 charge uses its original independent dual; this actual packet has the primal support generated by the original source embedding. -/
theorem phase_packet_charge (v : Stage9DEF.Source.Index→ℂ) :
    chargeMatrix sourcePhaseGaugeLie*ᵥphasePrimalPacket v=phasePrimalPacket (phaseColorProjection v) := by
  have primal:=congrArg Quantum.coordinates (phase_embedding_generated v)
  rw [←Quantum.matrix_action,map_smul] at primal
  change nativePrimal sourcePhaseGaugeLie*ᵥQuantum.coordinates (Stage9DEF.Compatibility.embed v)=
    (-Complex.I) • Quantum.coordinates (Stage9DEF.Compatibility.embed (phaseColorProjection v)) at primal
  change (Complex.I • Matrix.fromBlocks (nativePrimal sourcePhaseGaugeLie) 0 0
    ((nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ))) *ᵥ
    Sum.elim (Quantum.coordinates (Stage9DEF.Compatibility.embed v)) (fun _=>0)=
      Sum.elim (Quantum.coordinates (Stage9DEF.Compatibility.embed (phaseColorProjection v))) (fun _=>0)
  rw [Matrix.smul_mulVec,Matrix.fromBlocks_mulVec]
  have left : (Sum.elim (Quantum.coordinates (Stage9DEF.Compatibility.embed v))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inl=Quantum.coordinates (Stage9DEF.Compatibility.embed v) := rfl
  have right : (Sum.elim (Quantum.coordinates (Stage9DEF.Compatibility.embed v))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inr=0 := rfl
  simp only [left,right,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add,primal]
  funext i
  cases i with
  | inl i =>
    change Complex.I*((-Complex.I)*Quantum.coordinates (Stage9DEF.Compatibility.embed (phaseColorProjection v)) i)=_
    rw [←mul_assoc,mul_neg,Complex.I_mul_I,neg_neg,one_mul]
    rfl
  | inr i => simp

def phaseSeedPacket : FockFiber :=
  oneParticleFiber (phasePrimalPacket (phaseColorProjection (normalizedValues 0 0)))

theorem actual_seed_coordinates : seedCoordinates=phasePrimalPacket (normalizedValues 0 0) := by
  unfold seedCoordinates phasePrimalPacket
  rw [normalized_source]

/-- The actual canonical source seed's full phase charge is generated as its color0 packet, not supplied as an eigenvalue premise. -/
theorem actual_seed_phase_charge : quantized (chargeMatrix sourcePhaseGaugeLie) CanonicalCompletedSector.seed=phaseSeedPacket := by
  change quantized (chargeMatrix sourcePhaseGaugeLie) (oneParticleFiber seedCoordinates)=_
  rw [quantized_oneParticle,actual_seed_coordinates,phase_packet_charge]
  rfl

theorem actual_seed_phase_projection :
    quantized (chargeMatrix sourcePhaseGaugeLie) phaseSeedPacket=phaseSeedPacket := by
  unfold phaseSeedPacket
  rw [quantized_oneParticle,phase_packet_charge]
  congr 2
  funext i
  by_cases same : i.2=0
  · simp only [phaseColorProjection,if_pos same]
  · simp only [phaseColorProjection,if_neg same]

/-- The actual projected fiber packet is applied to the unchanged compact scalar profile. -/
def phaseSeedSection : ScalarTest→ₗ[ℂ]QuantumTest :=
  (TestFunction.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight phaseSeedPacket)).toLinearMap

theorem phase_seed_test_charge (f : ScalarTest) :
    chargeAction sourcePhaseGaugeLie (seedSection f)=phaseSeedSection f := by
  apply DFunLike.ext
  intro z
  change quantized (chargeMatrix sourcePhaseGaugeLie) (f z • CanonicalCompletedSector.seed)=f z • phaseSeedPacket
  rw [map_smul,actual_seed_phase_charge]

theorem phase_seed_test_projection (f : ScalarTest) :
    chargeAction sourcePhaseGaugeLie (phaseSeedSection f)=phaseSeedSection f := by
  apply DFunLike.ext
  intro z
  change quantized (chargeMatrix sourcePhaseGaugeLie) (f z • phaseSeedPacket)=f z • phaseSeedPacket
  rw [map_smul,actual_seed_phase_projection]

/-- Original profile completion preserves the source-computed 0/1 charge polynomial, without choosing a charge eigenprofile. -/
theorem prepared_phase_projection (profile : Profile) :
    chargeReader sourcePhaseGaugeLie (chargeReader sourcePhaseGaugeLie (prepared profile))=
      chargeReader sourcePhaseGaugeLie (prepared profile) := by
  refine core_dense.induction_on profile (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [prepared_core,chargeReader_core,phase_seed_test_charge,chargeReader_core,phase_seed_test_projection]

/-- The charged input is positively generated from the actual color0 seed packet and the retained scalar orbit; only their original sum is completed. -/
def phaseInputCore : ScalarTest→ₗ[ℂ]H :=
  (leg true 1 0).comp phaseSeedSection+
    Complex.I • embed.comp ((sourceJointScalarTest true 1 0).comp seedSection)

theorem phase_input_core_original : phaseInputCore=sourceJointInputCore true 1 0 := by
  apply LinearMap.ext
  intro f
  simp only [phaseInputCore,sourceJointInputCore,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.smul_apply,phase_seed_test_charge]

def phaseInputCompleted : Profile→L[ℂ]H := phaseInputCore.extendOfNorm core

theorem phase_input_completed_original : phaseInputCompleted=sourceJointInputCompleted true 1 0 :=
  congrArg (fun A : ScalarTest→ₗ[ℂ]H=>A.extendOfNorm core) phase_input_core_original

def actualPhaseInput (event : DressedEvent) : H :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*PhysicalEMDressedCharacter.emDressedCharacter true) •
    phaseInputCompleted (sourceProfile event.epsilon event.precision)

/-- Actual source normalization retains the computed seed packet plus the original scalar input, rather than assuming the created state is a joint-charge eigenstate. -/
theorem actual_creation_phase_input (event : DressedEvent) :
    chargeReader sourcePhaseGaugeLie (sourceDressedUnit event.epsilon event.precision)=
      (1/2:ℂ) • sourceDressedUnit event.epsilon event.precision+actualPhaseInput event := by
  rw [actualPhaseInput,phase_input_completed_original]
  exact ActualDressedJointWard.dressed_joint_unit_return event.epsilon event.precision

/-- This same prepared background carries the source-generated charge packet into the complete joint Gauss representation. -/
theorem actual_background_phase_projection (event : DressedEvent) :
    chargeReader sourcePhaseGaugeLie
        (chargeReader sourcePhaseGaugeLie (prepared (sourceProfile event.epsilon event.precision)))=
      chargeReader sourcePhaseGaugeLie (prepared (sourceProfile event.epsilon event.precision)) :=
  prepared_phase_projection _

end LowEnergy.GaussComposite.ActualDressedConstraintEndpoint
