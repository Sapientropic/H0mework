import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Disposition

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.ModelSpan
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private word_event from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Disposition
open private inventory_packet_transport from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Source
namespace CA
export ActualCofinalCommonAction (site siteAction WordInInventory actual_source_word_step)
end CA
namespace RM
export ActualCofinalResidualModelSplice (packetWordTransport)
end RM
namespace W
export NativeSigma.Writeback (nativeTrace nativeBoundary bornWord receiptSelected)
end W
namespace Born
export ActualNativeRelationTransport (bornStock born_stock paid_in_born bornHistory new_relation_in_born)
end Born
namespace Paid
export SourceOperationPaidRelations (words paid_boundary)
end Paid
local instance spanGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
attribute [local irreducible] AS.localNativeReceipt

def SourceInventoryAt (native : NativeSigma.NativePacket) : Prop :=
 (AS.bornAfterNative native).2.1.1.inventory=
 some (Born.bornStock (W.receiptSelected native) native.2.2.1)

private theorem native_inventory (native : NativeSigma.NativePacket) : SourceInventoryAt native := by
 simpa only [SourceInventoryAt,AS.bornAfterNative,AS.localNativeReceipt,W.receiptSelected] using
  Born.born_stock (W.receiptSelected native) native.2.2.1

def SourceClosureAt (native : NativeSigma.NativePacket) : Prop :=
 W.bornWord native (W.nativeBoundary native)∈
 (Born.bornHistory (W.receiptSelected native) native.2.2.1).relationClosure

private theorem native_closure (native : NativeSigma.NativePacket) : SourceClosureAt native :=
 Born.new_relation_in_born (W.receiptSelected native) native.2.2.1

private theorem native_step_member (native : NativeSigma.NativePacket) (word)
 (belongs : word∈Paid.words (W.nativeTrace native)) :
 PresentedRelationEventAt.relation (W.bornWord native word)∈
 (Born.bornStock (W.receiptSelected native) native.2.2.1).trace := by
 apply Born.paid_in_born
 exact word_event (W.nativeTrace native) word belongs

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev native := originalNative observation nontrivial half depth (ordinal+1)
abbrev sourcePacket := AS.bornAfterNative (native observation nontrivial half depth ordinal)

theorem packet_site : sourcePacket observation nontrivial half depth ordinal=
 CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2) :=
 (original_next_packet observation nontrivial half depth (ordinal+1)).symm

abbrev boundary := W.bornWord (native observation nontrivial half depth ordinal)
 (W.nativeBoundary (native observation nontrivial half depth ordinal))
abbrev sourceSteps := Paid.words (W.nativeTrace (native observation nontrivial half depth ordinal))
def sourceStock := Born.bornStock (W.receiptSelected (native observation nontrivial half depth ordinal))
 (native observation nontrivial half depth ordinal).2.2.1

def wordTransport := (RM.packetWordTransport (packet_site observation nontrivial half depth ordinal)).toLinearMap.comp
 (W.bornWord (native observation nontrivial half depth ordinal))
def siteWord := RM.packetWordTransport (packet_site observation nontrivial half depth ordinal)
 (boundary observation nontrivial half depth ordinal)
def siteSteps := (sourceSteps observation nontrivial half depth ordinal).map
 (wordTransport observation nontrivial half depth ordinal)

/-- The complete boundary is carried in the actual born inventory's generated relation closure. -/
theorem source_closure : SourceClosureAt (native observation nontrivial half depth ordinal) :=
 native_closure _

theorem source_inventory : SourceInventoryAt (native observation nontrivial half depth ordinal) :=
 native_inventory _

private theorem source_step_member (word)
 (belongs : word∈sourceSteps observation nontrivial half depth ordinal) :
 PresentedRelationEventAt.relation
  (W.bornWord (native observation nontrivial half depth ordinal) word)∈
 (sourceStock observation nontrivial half depth ordinal).trace :=
 native_step_member (native observation nontrivial half depth ordinal) word belongs

private theorem site_step_member (word)
 (belongs : word∈sourceSteps observation nontrivial half depth ordinal) :
 CA.WordInInventory
  (CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2))
  (wordTransport observation nontrivial half depth ordinal word) :=
 inventory_packet_transport (packet_site observation nontrivial half depth ordinal) _
  ⟨sourceStock observation nontrivial half depth ordinal,source_inventory observation nontrivial half depth ordinal,
   source_step_member observation nontrivial half depth ordinal word belongs⟩

/-- The original ordered paid Step list generates the whole transported boundary. -/
theorem boundary_paid_sum : siteWord observation nontrivial half depth ordinal=
 (siteSteps observation nontrivial half depth ordinal).sum := by
 have paid := Paid.paid_boundary (W.nativeTrace (native observation nontrivial half depth ordinal))
 change (sourceSteps observation nontrivial half depth ordinal).sum=
  W.nativeBoundary (native observation nontrivial half depth ordinal) at paid
 exact (congrArg (wordTransport observation nontrivial half depth ordinal) paid.symm).trans
  (map_list_sum _ _)

/-- Span membership retains all actual Step events rather than inventing a boundary event. -/
theorem boundary_source_span : siteWord observation nontrivial half depth ordinal∈Submodule.span ℤ
 {word | CA.WordInInventory
  (CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)) word} := by
 rw [boundary_paid_sum]
 let closed := Submodule.span ℤ {word | CA.WordInInventory
  (CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)) word}
 have sumIn : ∀ words : List (type_of% (siteWord observation nontrivial half depth ordinal)),
  (∀ word∈words,word∈closed)→words.sum∈closed := by
  intro words
  induction words with
  | nil => intro _; exact closed.zero_mem
  | cons word tail previous =>
   intro present
   exact closed.add_mem (present word List.mem_cons_self)
    (previous (fun entry member=>present entry (List.mem_cons_of_mem word member)))
 apply sumIn
 intro word member
 obtain ⟨original,belongs,rfl⟩:=List.mem_map.mp member
 exact Submodule.subset_span (site_step_member observation nontrivial half depth ordinal original belongs)

abbrev stepWord (index : Fin (sourceSteps observation nontrivial half depth ordinal).length) :=
 wordTransport observation nontrivial half depth ordinal
  ((sourceSteps observation nontrivial half depth ordinal).get index)

theorem step_inventory (index : Fin (sourceSteps observation nontrivial half depth ordinal).length) :
 CA.WordInInventory
  (CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2))
  (stepWord observation nontrivial half depth ordinal index) :=
 site_step_member observation nontrivial half depth ordinal _ (List.get_mem _ index)

/-- Every generated paid Step is consumed by the existing actual source action and whole span. -/
theorem actual_paid_step (index : Fin (sourceSteps observation nontrivial half depth ordinal).length) :
 type_of% (CA.actual_source_word_step (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (stepWord observation nontrivial half depth ordinal index)
  (step_inventory observation nontrivial half depth ordinal index)) :=
 CA.actual_source_word_step _ _ _ _ _ _ (step_inventory observation nontrivial half depth ordinal index)

/-- The complete action is the linear sum of those same ordered source-generated steps. -/
theorem boundary_action_sum :
 CA.siteAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2) (siteWord observation nontrivial half depth ordinal)=
 ((siteSteps observation nontrivial half depth ordinal).map
  (CA.siteAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl (ordinal+2))).sum :=
 (congrArg (CA.siteAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2))
  (boundary_paid_sum observation nontrivial half depth ordinal)).trans (map_list_sum _ _)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.ModelSpan
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
