import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Installation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open Complex BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local instance sourcePriceBaseGroups (initial : Nat) : ∀ target,AddCommGroup (L.Value (PairValue OriginalR.C.Value) initial target) :=
 L.groups (PairValue OriginalR.C.Value) initial
local instance sourcePriceOriginGroups (initial origin : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin target) :=
 L.groups (L.Value (PairValue OriginalR.C.Value) initial) origin
local instance sourcePriceRuntimeGroups (initial origin grade : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade target) :=
 L.groups (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade
variable (initial origin : Nat)
variable (mother : SF.Factory (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) OriginalR.C.Var ())
variable (packet : AS.AdmissionPacket (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) (X:=OriginalR.C.Var) (s:=()))
attribute [local irreducible] completeResidualRWholeTotal completeResidualRInherited completeResidualRReceived completeReceivedRQuartet

/-- All Pa, unit, signed-shell and invisible terms of the original R act on this exact received residual field. -/
theorem complete_received_R_full_four_terms (shift : ℝ) :
 OriginalKFullSourceRAction.OldR.fourTerms observation nontrivial half shift (completeActualResidualField initial origin packet)=
 burnolMultiplicativeDilation shift (completeReceivedRQuartet observation nontrivial half initial origin mother packet).1.1 := by
 rw [complete_received_R_four_feet]
 exact OriginalKFullSourceRAction.complete_four_term_source _ _ _ _ _

/-- The original operator prices the complete received source quartet against its actual residual input. -/
theorem complete_received_R_source_price :
 ‖completeReceivedRQuartet observation nontrivial half initial origin mother packet‖≤
 ‖OriginalR.variableAction observation nontrivial half‖*‖completeActualResidualRInput initial origin packet‖ := by
 rw [complete_received_R_four_feet]
 exact (OriginalR.variableAction observation nontrivial half).le_opNorm _

/-- The whole price keeps the native inherited contribution in addition to the relation-generated R quartet. -/
theorem complete_R_whole_source_price :
 ‖completeRSourceRead initial origin packet.1
  (completeResidualRWholeTotal observation nontrivial half initial origin mother packet)‖≤
 ‖OriginalR.variableAction observation nontrivial half‖*‖completeActualResidualRInput initial origin packet‖+
 ‖completeRSourceRead initial origin packet.1
  (completeResidualRInherited observation nontrivial half initial origin mother packet)‖ := by
 have total:=congrArg (completeRSourceRead initial origin packet.1)
  (complete_R_whole_partition observation nontrivial half initial origin mother packet)
 rw [map_add] at total
 rw [total]
 have own:=complete_received_R_source_price observation nontrivial half initial origin mother packet
 unfold completeReceivedRQuartet at own
 exact (norm_add_le _ _).trans (add_le_add own (le_refl _))

/-- The physical projection and its exact outside residual pay their own complete two-source prices. -/
theorem complete_R_physical_outside_prices :
 let full:=(completeRSourceRead initial origin packet.1
  (completeResidualRWholeTotal observation nontrivial half initial origin mother packet)).1.1
 let own:=(completeReceivedRQuartet observation nontrivial half initial origin mother packet).1.1
 let inherited:=(completeRSourceRead initial origin packet.1
  (completeResidualRInherited observation nontrivial half initial origin mother packet)).1.1
 ‖burnolEvenAmbientProjection full‖≤‖burnolEvenAmbientProjection own‖+‖burnolEvenAmbientProjection inherited‖ ∧
 ‖full-burnolEvenAmbientProjection full‖≤
 ‖own-burnolEvenAmbientProjection own‖+‖inherited-burnolEvenAmbientProjection inherited‖ := by
 dsimp only
 rcases complete_R_physical_and_outside observation nontrivial half initial origin mother packet with ⟨physical,outside⟩
 constructor
 · rw [physical]
   exact norm_add_le _ _
 · rw [outside]
   exact norm_add_le _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
