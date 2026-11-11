import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRInverseKernel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.BornActionConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre
open BurnolPhysicalState
namespace D
export OriginalKCombFirstFullSourceDynamics (input raw next_pair)
end D
namespace P
export OriginalKCombPhysicalAction (R physicalProjection physicalRemainder)
end P
namespace Full
export OriginalKCombFullResidualAction (branches split_complete complete_of_branches)
end Full
namespace Inv
export OriginalKCombCofinalInverseAction (inverse inverse_R pairTotal)
end Inv
namespace H
export SourceGeneratedActionObservationHistory
 (Model sourceMap projection modelAction modelReadout modelReadout_projection
  modelAction_source kernel_le_observer_kernel model_fibre_iff)
end H
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

abbrev SourcePair := BurnolL2 × BurnolL2
abbrev Branches := SourcePair × SourcePair

def splitR : BurnolL2 →ₗ[ℂ] SourcePair :=
 (P.physicalProjection.toLinearMap.comp (P.R observation nontrivial half).toLinearMap).prod
  (P.physicalRemainder.toLinearMap.comp (P.R observation nontrivial half).toLinearMap)

/-- The observer is the original source code's four output branches. -/
def sourceBranches : SourcePair →ₗ[ℂ] Branches :=
 ((splitR observation nontrivial half).comp (LinearMap.fst ℂ _ _)).prod
  ((splitR observation nontrivial half).comp (LinearMap.snd ℂ _ _))

def sourceStep : SourcePair →ₗ[ℂ] SourcePair :=
 (splitR observation nontrivial half).comp Inv.pairTotal

def branchReadback : Branches →ₗ[ℂ] SourcePair :=
 ((Inv.inverse observation nontrivial half).comp
   (Inv.pairTotal.comp (LinearMap.fst ℂ _ _))).prod
  ((Inv.inverse observation nontrivial half).comp
   (Inv.pairTotal.comp (LinearMap.snd ℂ _ _)))

theorem source_branches_readback (source : SourcePair) :
 branchReadback observation nontrivial half (sourceBranches observation nontrivial half source)=source := by
 change (Inv.inverse observation nontrivial half
  (P.physicalProjection (P.R observation nontrivial half source.1)+
   P.physicalRemainder (P.R observation nontrivial half source.1)),
  Inv.inverse observation nontrivial half
  (P.physicalProjection (P.R observation nontrivial half source.2)+
   P.physicalRemainder (P.R observation nontrivial half source.2)))=source
 rw [Full.split_complete,Full.split_complete,Inv.inverse_R,Inv.inverse_R]

abbrev SourceModel := H.Model (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)

def modelReadback : SourceModel observation nontrivial half →ₗ[ℂ] SourcePair :=
 (branchReadback observation nontrivial half).comp
  (H.modelReadout (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))

theorem model_readback_source (source : SourcePair) :
 modelReadback observation nontrivial half
  (H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half) source)=source := by
 change branchReadback observation nontrivial half
  (H.modelReadout _ _ (H.projection _ _ source))=source
 rw [H.modelReadout_projection,source_branches_readback]

/-- The generic complete-future kernel is eliminated by the actual R branch output,
not by a hidden copy of the source or a Pa observability premise. -/
theorem full_action_history_kernel :
 LinearMap.ker (H.sourceMap (sourceStep observation nontrivial half)
  (sourceBranches observation nontrivial half))=⊥ := by
 apply le_antisymm
 · intro source member
   have output := H.kernel_le_observer_kernel
    (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half) member
   have recovered := congrArg (branchReadback observation nontrivial half) output
   rw [source_branches_readback,map_zero] at recovered
   change source=0
   exact recovered
 · exact bot_le

variable (depth : Nat)

theorem actual_source_step (ordinal : Nat) :
 sourceStep observation nontrivial half (D.input observation nontrivial half depth ordinal)=
  D.input observation nontrivial half depth (ordinal+1) :=
 (D.next_pair observation nontrivial half depth ordinal).symm

theorem actual_source_iterate (ordinal steps : Nat) :
 ((sourceStep observation nontrivial half)^steps) (D.input observation nontrivial half depth ordinal)=
  D.input observation nontrivial half depth (ordinal+steps) := by
 induction steps with
 | zero => rfl
 | succ steps previous =>
  rw [pow_succ']
  change sourceStep observation nontrivial half
   (((sourceStep observation nontrivial half)^steps) (D.input observation nontrivial half depth ordinal))=_
  rw [previous,actual_source_step,Nat.add_assoc]

theorem model_iterate_source (source : SourcePair) (steps : Nat) :
 ((H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))^steps)
  (H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half) source)=
 H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
  (((sourceStep observation nontrivial half)^steps) source) := by
 induction steps with
 | zero => rfl
 | succ steps previous =>
  rw [pow_succ',pow_succ']
  change H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
   (((H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))^steps)
    (H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half) source))=
   H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
    (sourceStep observation nontrivial half (((sourceStep observation nontrivial half)^steps) source))
  rw [previous,H.modelAction_source]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
