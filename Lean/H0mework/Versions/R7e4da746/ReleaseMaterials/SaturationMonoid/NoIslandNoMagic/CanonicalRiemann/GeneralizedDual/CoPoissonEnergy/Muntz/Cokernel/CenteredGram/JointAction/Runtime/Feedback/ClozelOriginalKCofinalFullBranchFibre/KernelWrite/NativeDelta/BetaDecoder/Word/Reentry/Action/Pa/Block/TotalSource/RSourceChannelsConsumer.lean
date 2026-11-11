import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RSourceStepConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceCoupledChannels
open BurnolPhysicalState
open scoped InnerProductSpace
namespace Actual
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStepConsumer
 (originalRead)
end Actual
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
 (originalPoint original_action)
end Physical
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
 (physicalUpdated original_updated_total)
end Recurrence
namespace D
export OriginalKCombFirstFullSourceDynamics (raw raw_successor)
end D
namespace PA
export OriginalKCombCofinalPaAction (Q)
end PA
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKSourceResolventReconstruction
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance channelsComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def channels (value : BurnolL2) : BurnolL2 × BurnolL2 :=
 ((PA.Q value : BurnolL2),outside value)

private theorem channels_sub (left right : BurnolL2) :
 channels (left-right)=channels left-channels right := by
 apply Prod.ext <;> simp only [channels,map_sub,Submodule.coe_sub,Prod.fst_sub,Prod.snd_sub]

def sourceUpdate (c : BurnolCompletedMellinCoordinate) (unit : BurnolL2)
 (coefficient : ℂ) (value : BurnolL2) : BurnolL2 × BurnolL2 :=
 (coefficient • unit+
    (PA.Q (burnolDirectRightResolventCLM c (PA.Q value : BurnolL2)) : BurnolL2)+
    (-2*inner ℂ (hPowerPhysicalCorrection c) (outside value)) • generatedK (barC c),
  outside (burnolDirectRightResolventCLM c (outside value))+
    (-2*inner ℂ (fourierL2 (generatedK c)) (PA.Q value : BurnolL2)) • physicalOutsideColumn c)

private theorem sourceUpdate_sub (c : BurnolCompletedMellinCoordinate) (unit : BurnolL2)
 (a b : ℂ) (left right : BurnolL2) :
 sourceUpdate c unit (a-b) (left-right)=sourceUpdate c unit a left-sourceUpdate c unit b right := by
 apply Prod.ext
 · simp only [sourceUpdate,Prod.fst_sub,map_sub,Submodule.coe_sub,inner_sub_right,mul_sub,sub_smul]
   module
 · simp only [sourceUpdate,Prod.snd_sub,map_sub,Submodule.coe_sub,inner_sub_right,mul_sub,sub_smul]
   module

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "unit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth

private theorem original_source_channels (index : Nat) :
 channels (D.raw observation nontrivial half depth (index+1))=
 sourceUpdate c unit (alpha index) (D.raw observation nontrivial half depth index) :=
 actual_Q_outside_coupled_sources observation nontrivial half depth index

theorem actual_point_source : Physical.originalPoint observation nontrivial half depth ordinal=
 D.raw observation nontrivial half depth ((ordinal+3)+1)-
 D.raw observation nontrivial half depth ((ordinal+1)+1) := by
 rw [Physical.original_action,Recurrence.original_updated_total,map_sub,
   ←D.raw_successor,←D.raw_successor]

theorem original_point_channels :
 channels (Physical.originalPoint observation nontrivial half depth ordinal)=
 sourceUpdate c unit (alpha (ordinal+3)-alpha (ordinal+1))
  (Recurrence.physicalUpdated observation nontrivial half depth ordinal) := by
 have actual := congrArg₂ (fun left right : BurnolL2×BurnolL2=>left-right)
  (original_source_channels observation nontrivial half depth (ordinal+3))
  (original_source_channels observation nontrivial half depth (ordinal+1))
 rw [←channels_sub] at actual
 rw [actual_point_source]
 exact actual.trans ((sourceUpdate_sub c unit _ _ _ _).symm.trans
  (congrArg (sourceUpdate c unit (alpha (ordinal+3)-alpha (ordinal+1)))
   (Recurrence.original_updated_total observation nontrivial half depth ordinal).symm))

private def consumePoint {point : BurnolL2}
 (same : point=Physical.originalPoint observation nontrivial half depth ordinal) :=
 PProd.mk point ((congrArg channels same).trans
  (original_point_channels observation nontrivial half depth ordinal))

private def ResultAt :=
 Σ' actual : type_of% (Actual.originalRead observation nontrivial half depth ordinal),
 PProd (actual=Actual.originalRead observation nontrivial half depth ordinal)
  (type_of% (consumePoint observation nontrivial half depth ordinal actual.2.2.2.1))

attribute [local irreducible] ResultAt

opaque read : ResultAt observation nontrivial half depth ordinal := by
 unfold ResultAt
 let actual := Actual.originalRead observation nontrivial half depth ordinal
 exact ⟨actual,rfl,consumePoint observation nontrivial half depth ordinal actual.2.2.2.1⟩

end OriginalRSourceCoupledChannels
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
