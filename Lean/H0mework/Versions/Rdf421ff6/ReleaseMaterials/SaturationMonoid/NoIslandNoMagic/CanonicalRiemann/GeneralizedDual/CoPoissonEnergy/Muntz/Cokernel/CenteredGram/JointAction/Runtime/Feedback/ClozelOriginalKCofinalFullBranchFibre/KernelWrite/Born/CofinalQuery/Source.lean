import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.CofinalQuery.Effect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.ConfiguredStock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace CA
export ActualCofinalCommonAction (WordInInventory)
end CA
namespace CS
export ActualCofinalCommonAction.ConfiguredStock (nextWord nextEvent source_inventory)
end CS
namespace P
export SourceOperationPaidRelations (words exposure events_trace paid_boundary)
end P
attribute [local irreducible] AS.localNativeReceipt

section ExactSource
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance queryGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
private abbrev PairWordAt (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :=
 Formal ℤ (PairValue (L.Value W packet.1)) X ()
private def packetQueryWord
 {first second : AS.AdmissionPacket (W:=W) (X:=X) (s:=())} (same : first=second) :
 PairWordAt first ≃ₗ[ℤ] PairWordAt second := by
 cases same
 exact LinearEquiv.refl ℤ _

private theorem configured_query_words
 (factory : F.Factory W X ()) (initial : F.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=())) (language : cfg.LowVar=X)
 (ordinal : Nat) (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (same : packet=CA.site factory initial cfg language ordinal)
 (stock : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X ())))
 (written : packet.2.2.1.nextPairInventory packet.2.1.1=some stock)
 (queryWords : List (PairWordAt packet))
 (contains : ∀ word∈queryWords,PresentedRelationEventAt.relation word∈stock.trace) :
 ∃ targetStock,(CA.site factory initial cfg language (ordinal+1)).2.1.1.inventory=some targetStock ∧
 ∀ word∈queryWords,PresentedRelationEventAt.relation
  (CS.nextWord factory initial cfg language ordinal (packetQueryWord same word))∈targetStock.trace := by
 cases same
 have generated:=CS.source_inventory factory initial cfg language ordinal stock written
 obtain ⟨targetStock,present,_⟩:=generated.1
 refine ⟨targetStock,present,?_⟩
 intro word belongs
 obtain ⟨other,presentOther,member⟩:=generated.2 word (contains word belongs)
 have stockEq:other=targetStock:=Option.some.inj (presentOther.symm.trans present)
 exact stockEq ▸ member
end ExactSource

private theorem paid_relation_exposed
 {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
 {environment : Env Value Var} {before after : Expr Value Var ()}
 (trace : Trace environment before after) (word) (belongs : word∈P.words trace) :
 PresentedRelationEventAt.relation word∈(P.exposure trace).trace := by
 apply List.mem_cons_of_mem
 change PresentedRelationEventAt.relation word∈RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events trace)
 exact Eq.mpr (congrArg (fun events => PresentedRelationEventAt.relation word∈events)
  (P.events_trace trace)) (List.mem_map.mpr ⟨word,belongs,rfl⟩)

section Original
local instance originalGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev sourcePacket := MacroNext.bornPacket observation nontrivial half depth ordinal

theorem source_site : sourcePacket observation nontrivial half depth ordinal=
 CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+1) :=
 (Admissions.packetAt_successor (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal).symm

abbrev queryWords := P.words (RelationAction.queryTrace observation nontrivial half depth ordinal)

/-- Only the exact source packet/language transport moves the entire original query word. -/
def queryTransport : PairWordAt (sourcePacket observation nontrivial half depth ordinal) →ₗ[ℤ]
 F.Words (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2) :=
 (CS.nextWord (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+1)).comp
  (packetQueryWord (source_site observation nontrivial half depth ordinal)).toLinearMap

def queryBoundary := queryTransport observation nontrivial half depth ordinal
 (RelationAction.sourceBoundary observation nontrivial half depth ordinal)

/-- The complete paid boundary keeps its actual ordered list of all source Step relations. -/
theorem boundary_paid_sum : queryBoundary observation nontrivial half depth ordinal=
 ((queryWords observation nontrivial half depth ordinal).map
  (queryTransport observation nontrivial half depth ordinal)).sum := by
 exact (congrArg (queryTransport observation nontrivial half depth ordinal)
  (P.paid_boundary (RelationAction.queryTrace observation nontrivial half depth ordinal))).symm.trans
  (map_list_sum _ _)

/-- The original selected query is preserved by the actual same-born installed Joint. -/
theorem original_query_relation_written (word)
 (belongs : word∈queryWords observation nontrivial half depth ordinal) :
 PresentedRelationEventAt.relation word∈(installedWritten observation nontrivial half depth ordinal).trace := by
 apply Eq.mpr (congrArg (fun inventory => PresentedRelationEventAt.relation word∈inventory.trace)
  (installed_written observation nontrivial half depth ordinal))
 apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves
 exact original_query_trace_written observation nontrivial half depth ordinal _
  (paid_relation_exposed (RelationAction.queryTrace observation nontrivial half depth ordinal) word belongs)

/-- All original paid query relations enter one actual next-site stock. -/
theorem actual_query_stock :
 ∃ targetStock,(CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)).2.1.1.inventory=some targetStock ∧
 ∀ word∈queryWords observation nontrivial half depth ordinal,PresentedRelationEventAt.relation
  (queryTransport observation nontrivial half depth ordinal word)∈targetStock.trace := by
 obtain ⟨carried,written,preserved⟩:=MacroNext.actual_written_source_stock observation nontrivial half depth ordinal
 exact configured_query_words (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+1)
  (sourcePacket observation nontrivial half depth ordinal) (source_site observation nontrivial half depth ordinal)
  carried written (queryWords observation nontrivial half depth ordinal)
  (fun word belongs=>preserved _ (original_query_relation_written observation nontrivial half depth ordinal word belongs))

theorem actual_query_word_inventory (word)
 (belongs : word∈queryWords observation nontrivial half depth ordinal) :
 CA.WordInInventory
  (CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2))
  (queryTransport observation nontrivial half depth ordinal word) := by
 obtain ⟨stock,present,member⟩:=actual_query_stock observation nontrivial half depth ordinal
 exact ⟨stock,present,member word belongs⟩

/-- Each real paid Step relation triggers the original source action and its complete whole span. -/
theorem actual_query_word_step (word)
 (belongs : word∈queryWords observation nontrivial half depth ordinal) :
 type_of% (CA.actual_source_word_step (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (queryTransport observation nontrivial half depth ordinal word)
  (actual_query_word_inventory observation nontrivial half depth ordinal word belongs)) :=
 CA.actual_source_word_step _ _ _ _ _ _
  (actual_query_word_inventory observation nontrivial half depth ordinal word belongs)

end Original
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
