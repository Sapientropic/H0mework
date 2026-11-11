import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalResidual
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance residualComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Parent
export OriginalKDirectRCofinalDivision
 (sourceResponse sourceCoefficient sourceUnit sourceReturn source_response_Q actual_R_source_split)
end Parent
namespace D
export OriginalKCombFirstFullSourceDynamics (raw input)
end D
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace PA
export OriginalKCombCofinalPaAction (actualPa E Q invisible invisible_mem actual_complete_reconstruction)
end PA

theorem invisible_add (left right : BurnolL2) :
 PA.invisible (left+right)=PA.invisible left+PA.invisible right := by
 unfold PA.invisible
 simp only [map_add,Submodule.coe_add]
 abel

theorem invisible_physical (value : BurnolPaAmbientCarrier) :
 PA.invisible (value : BurnolL2)=
 (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection value : BurnolL2) := by
 change (value : BurnolL2)-
  (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
   (burnolEvenAmbientProjection (value : BurnolL2)) : BurnolL2)=_
 have physical : burnolEvenAmbientProjection (value : BurnolL2)=value :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [physical]
 apply sub_eq_iff_eq_add.mpr
 have split:=congrArg (fun material : BurnolPaAmbientCarrier=>(material : BurnolL2))
  (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal value)
 simpa only [Submodule.coe_add,add_comm] using split.symm

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- Division supplies the forcing unit of the whole actual E-invisible residual; R acts on its complete current material. -/
theorem actual_residual_successor :
 PA.invisible (D.raw observation nontrivial half depth (ordinal+1))=
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
  (Parent.sourceUnit observation nontrivial half : BurnolL2)+
 PA.invisible (P.R observation nontrivial half
  (PA.invisible (D.raw observation nontrivial half depth ordinal))) := by
 have generated:=congrArg PA.invisible
  (Parent.actual_R_source_split observation nontrivial half depth ordinal)
 rw [invisible_add,invisible_physical,Parent.source_response_Q] at generated
 simpa only [Submodule.coe_smul] using generated

/-- The complete residual still contains both its physical Q part and the original outside-P inventory. -/
theorem actual_residual_inventory :
 PA.invisible (D.raw observation nontrivial half depth (ordinal+1))=
 (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)+
 (D.input observation nontrivial half depth (ordinal+1)).2 := by
 have complete:=PA.actual_complete_reconstruction observation nontrivial half depth ordinal
 unfold PA.invisible
 change D.raw observation nontrivial half depth (ordinal+1)-
  (PA.actualPa observation nontrivial half depth (ordinal+1) : BurnolL2)=_
 calc
  _ = ((PA.actualPa observation nontrivial half depth (ordinal+1) : BurnolL2)+
    (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)+
    (D.input observation nontrivial half depth (ordinal+1)).2)-
    (PA.actualPa observation nontrivial half depth (ordinal+1) : BurnolL2) :=
   congrArg (fun material : BurnolL2=>material-
    (PA.actualPa observation nontrivial half depth (ordinal+1) : BurnolL2)) complete.symm
  _ = _ := by abel

/-- The next actual Q re-entry is generated from this residual update, with its full second R action retained. -/
theorem actual_reentry_successor :
 Parent.sourceReturn observation nontrivial half depth (ordinal+1)=
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
  PA.Q (P.R observation nontrivial half (Parent.sourceUnit observation nontrivial half : BurnolL2))+
 PA.Q (P.R observation nontrivial half
  (PA.invisible (P.R observation nontrivial half
   (PA.invisible (D.raw observation nontrivial half depth ordinal))))) := by
 have generated:=congrArg
  (fun material : BurnolL2=>PA.Q (P.R observation nontrivial half material))
  (actual_residual_successor observation nontrivial half depth ordinal)
 simpa only [Parent.sourceReturn,map_add,map_smul] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
