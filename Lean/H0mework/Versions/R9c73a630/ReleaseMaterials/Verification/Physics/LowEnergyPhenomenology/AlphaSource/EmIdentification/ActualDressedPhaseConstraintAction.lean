import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseSeedCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricResolvedConstraint

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
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
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
attribute [local instance] SourceRealScalarFock.branchOrder


open ActualDressedTemporalNormalization ActualDressedTemporalForm PreparationVacuumWeightedChargeActionWard
open PreparationVacuumElectricConstraint PreparationVacuumNoetherOrdinaryWard
attribute [local irreducible] sourceHamiltonian sourceApprox sourceTestApprox chargeAction
  emActionForm fullSourceAction leftCompressionDefect leftUncutDefect rightCompressionDefect rightUncutDefect

/-- The original complete configuration orbit, with its fixed reference momentum retained. -/
def phaseConstraintCore : QuantumTest→ₗ[ℂ]QuantumTest :=
  phaseDevAction+covariantMomentum phaseAmbientReference

/-- The normalized original-action form keeps the non-scalar phase normalizer and its full CAR pair subtraction inside the original configuration integral. -/
def phaseConstraintReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  -finiteRiesz F (fun i j=>emActionForm p (frameTest F i) (frameTest F j))

private theorem original_projected_charge (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    finiteRiesz F (fun i j=>emActionForm p (frameTest F i) (frameTest F j)) y=
      sourceApprox F (embed (chargeAction sourcePhaseGaugeLie (sourceTestApprox F y))) := by
  simp only [em_action_form]
  rw [sourceApprox_frame,sourceTestApprox_frame]
  simp only [finiteRiesz,sum_apply,smul_apply,InnerProductSpace.rankOne_apply,
    map_sum,map_smul,inner_sum,inner_smul_right,Finset.sum_smul,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold sourcePair
  rw [frameTest_embed]
  congr 1
  ring

/-- Same source F: this is the original normalized action integral's actual configuration-constraint insertion. -/
theorem phase_constraint_projected_action (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    phaseConstraintReader p F y=sourceApprox F (embed (phaseConstraintCore (sourceTestApprox F y))) := by
  simp only [phaseConstraintReader,neg_apply,original_projected_charge,phaseConstraintCore,
    phase_dev_gauss_return,LinearMap.neg_apply,map_neg]

/-- Its finite source projection is generated, rather than assumed charge invariant. -/
theorem phase_constraint_projected_charge (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    phaseConstraintReader p F= -(sourceApprox F*chargeReader sourcePhaseGaugeLie*sourceApprox F) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [phase_constraint_projected_action]
  simp only [phaseConstraintCore,phase_dev_gauss_return,LinearMap.neg_apply,map_neg,neg_apply]
  rw [←chargeReader_core,sourceTestApprox_embed]
  rfl

private theorem phase_core_action (p k : PhysicalMomentum) (f : QuantumTest) :
    fullSourceAction (p+k) (phaseConstraintCore f)-phaseConstraintCore (fullSourceAction p f)=
      -wardCore k sourcePhaseGaugeLie f := by
  have paid:=complete_source_constraint p k sourcePhaseGaugeLie f
  have source : fullSourceAction (p+k) (orbitAction sourcePhaseGaugeLie f)-
    orbitAction sourcePhaseGaugeLie (fullSourceAction p f)+wardCore k sourcePhaseGaugeLie f=0 := by
    simpa only [fullSourceAction] using! paid
  rw [phaseConstraintCore,phase_dev_reference_balance]
  exact eq_neg_iff_add_eq_zero.mpr source

/-- Positive original RHS: four full-action Ward terms and both genuine compression/uncut endpoint returns. -/
def phaseConstraintChannels (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) : H :=
  -sourceApprox F (embed
    (configurationTorque sourcePhaseGaugeLie (sourceTestApprox F y)+
      CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie (sourceTestApprox F y)+
      pairCurrent k sourcePhaseGaugeLie (sourceTestApprox F y)+
      yukawaTorque sourcePhaseGaugeLie (sourceTestApprox F y)))+
  leftCompressionDefect (p+k) F (phaseConstraintCore (sourceTestApprox F y))+
  leftUncutDefect (p+k) F (phaseConstraintCore (sourceTestApprox F y))-
  sourceApprox F (embed (phaseConstraintCore
    (rightCompressionDefect p F y+rightUncutDefect p F y)))

/-- The original full joint Hamiltonian computes the constraint endpoint through its actual source action; no Gauss-kernel or separate-domain assumption is introduced. -/
theorem phase_constraint_hamiltonian_return (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceHamiltonian (p+k) F (phaseConstraintReader p F y)-
      phaseConstraintReader p F (sourceHamiltonian p F y)=phaseConstraintChannels p k F y := by
  rw [phase_constraint_projected_action,phase_constraint_projected_action,leftAction_source,rightAction_source]
  simp only [map_add,sourceApprox_add]
  have action:=congrArg (fun f : QuantumTest=>sourceApprox F (embed f)) (phase_core_action p k (sourceTestApprox F y))
  simp only [map_sub,map_neg,sourceApprox_sub] at action
  unfold phaseConstraintChannels
  simp only [wardCore,LinearMap.add_apply] at action
  rw [←action]
  simp only [map_add,sourceApprox_add]
  abel

end LowEnergy.GaussComposite.ActualDressedConstraintEndpoint
