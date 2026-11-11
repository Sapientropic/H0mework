import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Physics
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open Complex BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance completePriceGroups {W : Unit→Type} [∀ target,AddCommGroup (W target)] (grade : Nat) :
 ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (initial origin : Nat)
variable (mother : SF.Factory (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) OriginalR.C.Var ())
variable (packet : AS.AdmissionPacket (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) (X:=OriginalR.C.Var) (s:=()))
attribute [local irreducible] completeResidualRWholeTotal completeResidualRInherited completeResidualRReceived

/-- The generated whole total retains the received relation R action and actual native inherited R effect. -/
theorem complete_R_whole_partition :
 completeResidualRWholeTotal observation nontrivial half initial origin mother packet=
 completeResidualRReceived observation nontrivial half initial origin mother packet+
 completeResidualRInherited observation nontrivial half initial origin mother packet := by
 unfold completeResidualRReceived
 abel

/-- The complete source quartet, not a free projected margin, pays every independent additive observer. -/
theorem complete_R_whole_observer {Result : Type} [AddCommGroup Result]
 (read : OriginalKFullSourceRAction.Prior.Branches→+Result) :
 read (completeRSourceRead initial origin packet.1
  (completeResidualRWholeTotal observation nontrivial half initial origin mother packet))=
 read (completeReceivedRQuartet observation nontrivial half initial origin mother packet)+
 read (completeRSourceRead initial origin packet.1
  (completeResidualRInherited observation nontrivial half initial origin mother packet)) :=
 (congrArg (fun value=>read (completeRSourceRead initial origin packet.1 value))
  (complete_R_whole_partition observation nontrivial half initial origin mother packet)).trans
 ((congrArg read (map_add (completeRSourceRead initial origin packet.1) _ _)).trans (read.map_add _ _))

/-- The actual native inherited source is the same R operator applied to its source increment, preserving all four feet. -/
theorem complete_R_inherited_four_feet :
 completeRSourceRead initial origin packet.1
 (completeResidualRInherited observation nontrivial half initial origin mother packet)=
 OriginalR.variableAction observation nontrivial half
 (completeRSourceRead initial origin packet.1
  (completeResidualTotalRole initial origin packet.1
   ((sourceResidualCode (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).effect
    (completeResidualRMaterial observation nontrivial half initial origin mother packet).environment
    (completeResidualRMaterial observation nontrivial half initial origin mother packet).increment))) :=
 (congrArg (completeRSourceRead initial origin packet.1)
  (complete_R_inherited_action observation nontrivial half initial origin mother packet)).trans
 (complete_R_source_action_read _ _ _ _ _ _ _)

/-- Physical and outside readers retain both received and inherited source prices. -/
theorem complete_R_physical_and_outside :
 let full:=(completeRSourceRead initial origin packet.1
  (completeResidualRWholeTotal observation nontrivial half initial origin mother packet)).1.1
 let own:=(completeReceivedRQuartet observation nontrivial half initial origin mother packet).1.1
 let inherited:=(completeRSourceRead initial origin packet.1
  (completeResidualRInherited observation nontrivial half initial origin mother packet)).1.1
 burnolEvenAmbientProjection full=burnolEvenAmbientProjection own+burnolEvenAmbientProjection inherited ∧
 full-burnolEvenAmbientProjection full=
 (own-burnolEvenAmbientProjection own)+(inherited-burnolEvenAmbientProjection inherited) := by
 have branch : (completeRSourceRead initial origin packet.1
  (completeResidualRWholeTotal observation nontrivial half initial origin mother packet)).1.1=
  (completeReceivedRQuartet observation nontrivial half initial origin mother packet).1.1+
  (completeRSourceRead initial origin packet.1
   (completeResidualRInherited observation nontrivial half initial origin mother packet)).1.1 :=
   (congrArg (fun value=>((completeRSourceRead initial origin packet.1) value).1.1)
    (complete_R_whole_partition observation nontrivial half initial origin mother packet)).trans
    (congrArg (fun value : OriginalKFullSourceRAction.Prior.Branches=>value.1.1)
     (map_add (completeRSourceRead initial origin packet.1) _ _))
 dsimp only
 rw [branch,map_add]
 exact ⟨rfl,by
  simp only [Submodule.coe_add]
  abel⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
