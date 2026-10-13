import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Material.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.ActorConsumer

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaSourceMaterialConsumerComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction









open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement

local instance sourceMaterialConsumerGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (producer : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

def actualMaterialActorBranches (h nextShift : ℝ) : SourceBranches :=
  OriginalKFullSourceRAction.CF.collapseValue (grade+1)
    ((ActorR.actualMaterial
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).increment () (language.symm ▸ ())) -
  actualInheritedSourceIncrement observation nontrivial half producer grade data sourceCfg language h nextShift (language.symm ▸ ())

def actualMaterialInheritedREffect (h nextShift : ℝ) : SourceBranches :=
  OriginalKFullSourceRAction.variableAction observation nontrivial half
    (actualInheritedSourceIncrement observation nontrivial half producer grade data sourceCfg language h nextShift (language.symm ▸ ()))

def actualMaterialREffect (h nextShift : ℝ) : SourceBranches :=
  OriginalKFullSourceRAction.CF.collapseValue (grade+1)
    ((ActorR.actualMaterial
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).raw.effect
      (ActorR.actualMaterial
        (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
        (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).environment
      (ActorR.actualMaterial
        (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
        (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).increment)

theorem actual_material_actor_branches (h nextShift : ℝ) :
    actualMaterialActorBranches observation nontrivial half producer grade data sourceCfg language h nextShift =
      actualSourceDeltaBranches observation nontrivial half h nextShift := by
  unfold actualMaterialActorBranches
  rw [actual_material_complete_source_increment]
  exact add_sub_cancel_left _ _

theorem actual_material_R_effect_partition (h nextShift : ℝ) :
    actualMaterialREffect observation nontrivial half producer grade data sourceCfg language h nextShift =
      actualMaterialInheritedREffect observation nontrivial half producer grade data sourceCfg language h nextShift +
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualMaterialActorBranches observation nontrivial half producer grade data sourceCfg language h nextShift) := by
  unfold actualMaterialREffect actualMaterialInheritedREffect
  rw [actual_material_complete_original_R_effect,actual_material_actor_branches]

/-- The actor's R field is read from the material's actual effect after retaining its inherited R stock. -/
theorem actual_material_actor_R_read (h nextShift : ℝ) :
    (actualMaterialREffect observation nontrivial half producer grade data sourceCfg language h nextShift -
      actualMaterialInheritedREffect observation nontrivial half producer grade data sourceCfg language h nextShift).1.1 =
      OriginalKFullSourceRResponse.Op.R observation nontrivial half
        (OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift) := by
  rw [actual_material_R_effect_partition,add_sub_cancel_left,actual_material_actor_branches]
  rfl

def actualMaterialSourceDelta (h nextShift : ℝ) : BurnolL2 :=
  OriginalKFullSourceRAction.originalField
    (actualMaterialActorBranches observation nontrivial half producer grade data sourceCfg language h nextShift)

def actualMaterialPaCoefficient (h nextShift : ℝ) : ℂ :=
  burnolPaResolventSourceCoefficient (actualWholePaDivisionCoordinate observation nontrivial half)
    (OriginalKCombCofinalPaAction.E (actualMaterialSourceDelta observation nontrivial half producer grade data sourceCfg language h nextShift))

def actualMaterialNonPaR (h nextShift : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (actualMaterialSourceDelta observation nontrivial half producer grade data sourceCfg language h nextShift -
      (OriginalKCombCofinalPaAction.E (actualMaterialSourceDelta observation nontrivial half producer grade data sourceCfg language h nextShift) : BurnolL2))

theorem actual_material_Pa_nonPa_R_read (h nextShift : ℝ) :
    actualMaterialPaCoefficient observation nontrivial half producer grade data sourceCfg language h nextShift =
      actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift ∧
    actualMaterialNonPaR observation nontrivial half producer grade data sourceCfg language h nextShift =
      actualNonPaNativeRUpdate observation nontrivial half h nextShift := by
  unfold actualMaterialPaCoefficient actualMaterialNonPaR actualMaterialSourceDelta
  rw [actual_material_actor_branches]
  exact ⟨rfl,rfl⟩

def actualMaterialCrossEffect (h nextShift : ℝ) : ℂ :=
  (actualOriginalCrossFactor observation nextShift - actualOriginalCrossFactor observation h) *
      actualWholePaPairSourcePrice observation nontrivial half h +
  actualOriginalCrossFactor observation nextShift *
    (star (actualMaterialPaCoefficient observation nontrivial half producer grade data sourceCfg language h nextShift / 2) *
      actualWholePaUnitPairPrice observation nontrivial half +
      OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
        (actualMaterialNonPaR observation nontrivial half producer grade data sourceCfg language h nextShift)) +
  star (actualOriginalCrossFactor observation nextShift - actualOriginalCrossFactor observation h) *
      actualWholePaSiblingSourcePrice observation nontrivial half h +
  star (actualOriginalCrossFactor observation nextShift) *
    ((actualMaterialPaCoefficient observation nontrivial half producer grade data sourceCfg language h nextShift / 2) *
      actualWholePaUnitSiblingPrice observation nontrivial half +
      OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
        (actualMaterialNonPaR observation nontrivial half producer grade data sourceCfg language h nextShift))

theorem actual_material_cross_effect_generated (h nextShift : ℝ) :
    actualMaterialCrossEffect observation nontrivial half producer grade data sourceCfg language h nextShift =
      actualWholePaRankSourceCharacterUpdate observation nontrivial half h nextShift := by
  unfold actualMaterialCrossEffect
  rw [(actual_material_Pa_nonPa_R_read observation nontrivial half producer grade data sourceCfg language h nextShift).1,
    (actual_material_Pa_nonPa_R_read observation nontrivial half producer grade data sourceCfg language h nextShift).2]
  rfl

/-- The independent fixed-actor Cross consumer reads the newly generated source component of this actual original R material. -/
theorem actual_cross_consumes_original_R_material (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half nextShift -
      OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualMaterialCrossEffect observation nontrivial half producer grade data sourceCfg language h nextShift := by
  rw [actual_material_cross_effect_generated]
  exact actual_original_cross_consumes_native_rank_update observation nontrivial half h nextShift nonnegative ordered

/-- The current reader retains the complete original five residuals while consuming the material's actual source component. -/
theorem actual_current_consumes_original_R_material (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift)
    (bounded : nextShift ≤ Real.log 2) (n : Nat) :
    (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half nextShift
        (nonnegative.trans ordered) bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half nextShift
        (nonnegative.trans ordered) bounded n) -
    (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative (ordered.trans bounded) n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative (ordered.trans bounded) n) =
      actualMaterialCrossEffect observation nontrivial half producer grade data sourceCfg language h nextShift := by
  rw [actual_material_cross_effect_generated]
  exact actual_current_consumes_native_rank_update observation nontrivial half h nextShift nonnegative ordered bounded n

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
