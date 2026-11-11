import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.PostDecoder.Adjacent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Model.Span

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.ModelDecoder
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
open private native_born_value from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source
open private collapse_native_add from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Consumer
open private total from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Source
namespace CA
export ActualCofinalCommonAction
 (site siteAction Model projection modelAction modelRead model_fibre actions)
end CA
namespace PD
export ActualCofinalCommonAction.PostDecoder (adjacentRead adjacent_read_source siteRead next_action_read)
end PD
namespace SA
export ActualCofinalSourceAction (sourceBorn sourceWordAction)
end SA
namespace RM
export ActualCofinalResidualModelSplice (packetWordTransport)
end RM
namespace W
export NativeSigma.Writeback
 (nativeInverseValue nativeBoundary bornWord bornValue retainedInNative admissionWord)
end W
namespace F
export ActualCofinalCommonAction.T (Factory Frame Programme Words CommonWords stageInventory)
end F
local instance modelDecoderGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private def packetValue {first second : NativeSigma.NativePacket} (same : first=second) :
 L.Value (PairValue C.Value) first.1 () ≃+ L.Value (PairValue C.Value) second.1 () := by
 cases same
 exact AddEquiv.refl _

private theorem packet_current_read {first second : NativeSigma.NativePacket} (same : first=second)
 (word : Formal ℤ (L.Value (PairValue C.Value) first.1) C.Var ()) :
 packetValue same.symm
  (evaluation (R:=ℤ) second.2.1.1.activeEnvironment (RM.packetWordTransport same word))=
 evaluation (R:=ℤ) first.2.1.1.activeEnvironment word := by cases same; rfl

private theorem packet_heq_read {first second : NativeSigma.NativePacket} (same : first=second)
 (left : L.Value (PairValue C.Value) first.1 ()) (right : L.Value (PairValue C.Value) second.1 ())
 (read : HEq right left) : packetValue same.symm right=left := by
 cases same
 exact eq_of_heq read

private theorem native_acted_read (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
 HEq (evaluation (R:=ℤ) (SA.sourceBorn factory packet).2.1.1.activeEnvironment
   (SA.sourceWordAction packet word))
  (evaluation (R:=ℤ) (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.1.1.activeEnvironment
   (W.admissionWord factory packet (liftMap (R:=ℤ) word))) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  rfl

private theorem packet_acted_read (factory : NativeSigma.NativeFactory)
 (initial : F.Frame (Value:=PairValue C.Value) (Var:=C.Var) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=PairValue C.Value) (PhysicalVar:=C.Var) (sort:=()))
 (language : cfg.LowVar=C.Var) (ordinal : Nat) (packet : NativeSigma.NativePacket)
 (same : packet=CA.site factory initial cfg language ordinal)
 (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
 HEq (evaluation (R:=ℤ) (CA.site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
   (CA.siteAction factory initial cfg language ordinal (RM.packetWordTransport same word)))
  (evaluation (R:=ℤ) (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.1.1.activeEnvironment
   (W.admissionWord factory packet (liftMap (R:=ℤ) word))) := by
 cases same
 exact (PD.next_action_read factory initial cfg language ordinal word).trans
  (native_acted_read factory _ word)

private theorem actual_updated_evaluation (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 Recurrence.actualUpdatedValue factory native=
 evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment
  (admittedBeta factory native) := rfl

private theorem packet_decoder_read (factory : NativeSigma.NativeFactory)
 (initial : F.Frame (Value:=PairValue C.Value) (Var:=C.Var) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=PairValue C.Value) (PhysicalVar:=C.Var) (sort:=()))
 (language : cfg.LowVar=C.Var) (ordinal : Nat) (native : NativeSigma.NativePacket)
 (currentSite : AS.bornAfterNative native=CA.site factory initial cfg language ordinal)
 (nextSite : AS.bornAfterNative (nextNative factory native)=CA.site factory initial cfg language (ordinal+1)) :
 packetValue nextSite.symm
  (evaluation (R:=ℤ) (CA.site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
   (CA.siteAction factory initial cfg language ordinal
    (RM.packetWordTransport currentSite (W.bornWord native (W.nativeBoundary native)))))=
 Recurrence.actualUpdatedValue factory native :=
 packet_heq_read nextSite _ _
  ((packet_acted_read factory initial cfg language ordinal (AS.bornAfterNative native) currentSite
   (W.bornWord native (W.nativeBoundary native))).trans
   (heq_of_eq (actual_updated_evaluation factory native).symm))

private theorem packet_model_decoder_read (factory : NativeSigma.NativeFactory)
 (initial : F.Frame (Value:=PairValue C.Value) (Var:=C.Var) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=PairValue C.Value) (PhysicalVar:=C.Var) (sort:=()))
 (language : cfg.LowVar=C.Var) (ordinal : Nat) (native : NativeSigma.NativePacket)
 (currentSite : AS.bornAfterNative native=CA.site factory initial cfg language ordinal)
 (nextSite : AS.bornAfterNative (nextNative factory native)=CA.site factory initial cfg language (ordinal+1)) :
 packetValue nextSite.symm
  ((PD.adjacentRead factory initial cfg language ordinal
   (CA.projection factory initial cfg language
    (DFinsupp.single ordinal
     (RM.packetWordTransport currentSite (W.bornWord native (W.nativeBoundary native)))))).2)=
 Recurrence.actualUpdatedValue factory native :=
 (congrArg (packetValue nextSite.symm)
  (congrArg Prod.snd (PD.adjacent_read_source factory initial cfg language ordinal
   (RM.packetWordTransport currentSite (W.bornWord native (W.nativeBoundary native)))))).trans
  (packet_decoder_read factory initial cfg language ordinal native currentSite nextSite)

attribute [local irreducible] AS.localNativeReceipt L.Value
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev native := ModelSpan.native observation nontrivial half depth ordinal
abbrev sourcePacket := ModelSpan.sourcePacket observation nontrivial half depth ordinal
abbrev sourceWords : F.CommonWords (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl :=
 DFinsupp.single (ordinal+2) (ModelSpan.siteWord observation nontrivial half depth ordinal)
def sourceModel := CA.projection (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
 (sourceWords observation nontrivial half depth ordinal)
def rawRead := PD.adjacentRead (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)

abbrev postPacket := AS.bornAfterNative
 (nextNative (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal))

theorem post_site : postPacket observation nontrivial half depth ordinal=
 CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+3) :=
 (congrArg AS.bornAfterNative (Rooting.native_successor observation nontrivial half depth (ordinal+1))).symm.trans
  (original_next_packet observation nontrivial half depth (ordinal+2)).symm

def currentValue (value : CA.Model (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) :=
 packetValue (ModelSpan.packet_site observation nontrivial half depth ordinal).symm
  ((rawRead observation nontrivial half depth ordinal value).1)

def postValue (value : CA.Model (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) :=
 packetValue (post_site observation nontrivial half depth ordinal).symm
  ((rawRead observation nontrivial half depth ordinal value).2)

theorem source_current_read :
 currentValue observation nontrivial half depth ordinal (sourceModel observation nontrivial half depth ordinal)=
 W.bornValue (native observation nontrivial half depth ordinal)
  (W.nativeInverseValue (native observation nontrivial half depth ordinal)) := by
 have read:=congrArg Prod.fst (PD.adjacent_read_source (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (ModelSpan.siteWord observation nontrivial half depth ordinal))
 exact (congrArg (packetValue (ModelSpan.packet_site observation nontrivial half depth ordinal).symm) read).trans
  ((packet_current_read (ModelSpan.packet_site observation nontrivial half depth ordinal)
    (ModelSpan.boundary observation nontrivial half depth ordinal)).trans
   (native_born_value (native observation nontrivial half depth ordinal)))

theorem source_post_read :
 postValue observation nontrivial half depth ordinal (sourceModel observation nontrivial half depth ordinal)=
 Recurrence.actualUpdatedValue (D.factory observation nontrivial half)
  (native observation nontrivial half depth ordinal) :=
 packet_model_decoder_read (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (native observation nontrivial half depth ordinal)
  (ModelSpan.packet_site observation nontrivial half depth ordinal)
  (post_site observation nontrivial half depth ordinal)

private def pairRead (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (before : L.Value (PairValue C.Value) packet.1 ())
 (after : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :=
 let retained:=W.retainedInNative factory packet before
 (retained,after-retained)

private def nativeBornValue (native : NativeSigma.NativePacket)
 (value : L.Value (PairValue C.Value) (AS.bornAfterNative native).1 ()) :
 L.Value (PairValue C.Value) native.1 () := value

def recoveredPair (value : CA.Model (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) :=
 pairRead (D.factory observation nontrivial half) (sourcePacket observation nontrivial half depth ordinal)
  (currentValue observation nontrivial half depth ordinal value)
  (nativeBornValue (nextNative (D.factory observation nontrivial half)
    (native observation nontrivial half depth ordinal))
   (postValue observation nontrivial half depth ordinal value))

private def RecoveredAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (pair : L.Value (PairValue C.Value) (nextNative factory native).1 ()×
  L.Value (PairValue C.Value) (nextNative factory native).1 ()) : Prop :=
 pair=(Recurrence.retained factory native,W.nativeInverseValue (nextNative factory native))

private def ActualPairAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (pair : L.Value (PairValue C.Value) (nextNative factory native).1 ()×
  L.Value (PairValue C.Value) (nextNative factory native).1 ()) : Prop :=
 pair=(residualEquivRange (updateInventory (R:=ℤ) (old factory native) (increment factory native))
  (canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native))
   (admittedBeta factory native))).val

private theorem pair_from_reads (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (before after : L.Value (PairValue C.Value) (nextNative factory native).1 ())
 (old : before=Recurrence.retained factory native)
 (updated : after=Recurrence.retained factory native+W.nativeInverseValue (nextNative factory native)) :
 (before,after-before)=(Recurrence.retained factory native,W.nativeInverseValue (nextNative factory native)) := by
 rw [old,updated]
 simp only [add_sub_cancel_left]

private theorem pair_from_source_reads (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (before : L.Value (PairValue C.Value) (AS.bornAfterNative native).1 ())
 (after : L.Value (PairValue C.Value) (AS.bornAfterNative (nextNative factory native)).1 ())
 (current : before=W.bornValue native (W.nativeInverseValue native))
 (post : after=Recurrence.actualUpdatedValue factory native)
 (updated : Recurrence.UpdatedAt factory native) :
 RecoveredAt factory native
  (pairRead factory (AS.bornAfterNative native) before (nativeBornValue (nextNative factory native) after)) :=
 pair_from_reads factory native _ _
  (congrArg (W.retainedInNative factory (AS.bornAfterNative native)) current)
  ((congrArg (nativeBornValue (nextNative factory native)) post).trans updated)

theorem original_recovered_pair : RecoveredAt (D.factory observation nontrivial half)
 (native observation nontrivial half depth ordinal)
 (recoveredPair observation nontrivial half depth ordinal (sourceModel observation nontrivial half depth ordinal)) :=
 pair_from_source_reads _ _ _ _ (source_current_read observation nontrivial half depth ordinal)
  (source_post_read observation nontrivial half depth ordinal)
  (Recurrence.original_updated_recurrence observation nontrivial half depth ordinal)

private theorem actual_from_recovered (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (pair : L.Value (PairValue C.Value) (nextNative factory native).1 ()×
  L.Value (PairValue C.Value) (nextNative factory native).1 ())
 (read : RecoveredAt factory native pair) (actual : Recurrence.PairAt factory native) :
 ActualPairAt factory native pair := read.trans actual.symm

theorem original_actual_pair : ActualPairAt (D.factory observation nontrivial half)
 (native observation nontrivial half depth ordinal)
 (recoveredPair observation nontrivial half depth ordinal (sourceModel observation nontrivial half depth ordinal)) :=
 actual_from_recovered _ _ _ (original_recovered_pair observation nontrivial half depth ordinal)
  (Recurrence.original_pair_recurrence observation nontrivial half depth ordinal)

/-- The complete future Model fibre supplies this actual decoder pair as a dependent readout. -/
theorem future_fibre_actual_pair
 (candidate : F.CommonWords (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) :
 (∀ history : List PUnit.{1},∀ target,
  F.stageInventory (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl target
   (SourceGeneratedActionWords.run (CA.actions (D.factory observation nontrivial half)
    (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) history candidate)=
  F.stageInventory (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl target
   (SourceGeneratedActionWords.run (CA.actions (D.factory observation nontrivial half)
    (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl) history
    (sourceWords observation nontrivial half depth ordinal))) →
 recoveredPair observation nontrivial half depth ordinal
  (CA.projection (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl candidate)=
 recoveredPair observation nontrivial half depth ordinal (sourceModel observation nontrivial half depth ordinal) := by
 intro allFuture
 exact congrArg (recoveredPair observation nontrivial half depth ordinal)
  ((CA.model_fibre (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl candidate
   (sourceWords observation nontrivial half depth ordinal)).mpr allFuture)

private theorem collapse_native_zero (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket) :
 NativeSigma.collapseNative factory packet (0 : L.Value (PairValue C.Value)
  (AS.nativeAfterAdmission factory packet).1 ())=0 := by
 have generated:=collapse_native_add factory packet 0 0
 simp only [add_zero] at generated
 exact add_eq_left.mp generated.symm

private theorem actual_zero_physical (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (zero : Recurrence.actualUpdatedValue factory native=0) :
 total (NativeSigma.collapseNative factory (AS.bornAfterNative native)
  (Recurrence.actualUpdatedValue factory native))=0 := by
 rw [zero,collapse_native_zero]
 simp only [total,Prod.fst_zero,Prod.snd_zero,zero_add]

private theorem packetValue_zero {first second : NativeSigma.NativePacket} (same : first=second) :
 packetValue same (0 : L.Value (PairValue C.Value) first.1 ())=0 := by
 cases same
 rfl

private theorem packet_action_zero (factory : NativeSigma.NativeFactory)
 (initial : F.Frame (Value:=PairValue C.Value) (Var:=C.Var) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=PairValue C.Value) (PhysicalVar:=C.Var) (sort:=()))
 (language : cfg.LowVar=C.Var) (ordinal : Nat) (packet : NativeSigma.NativePacket)
 (same : packet=CA.site factory initial cfg language (ordinal+1))
 (value : CA.Model factory initial cfg language)
 (zero : CA.modelAction factory initial cfg language value=0) :
 packetValue same.symm ((PD.adjacentRead factory initial cfg language ordinal value).2)=0 := by
 change packetValue same.symm
  (PD.siteRead factory initial cfg language [] (ordinal+1)
   (CA.modelAction factory initial cfg language value))=0
 rw [zero,map_zero]
 exact packetValue_zero same.symm

private theorem action_zero_post_zero
 (value : CA.Model (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl)
 (zero : CA.modelAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl value=0) :
 postValue observation nontrivial half depth ordinal value=0 :=
 packet_action_zero (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (postPacket observation nontrivial half depth ordinal) (post_site observation nontrivial half depth ordinal) value zero

/-- The existing Model action cannot erase this real beta update: its physical consumer is the original R-square Gram. -/
theorem original_action_nonzero :
 CA.modelAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (sourceModel observation nontrivial half depth ordinal)≠0 := by
 intro zero
 have readZero:=action_zero_post_zero observation nontrivial half depth ordinal
  (sourceModel observation nontrivial half depth ordinal) zero
 have nativeZero:= (source_post_read observation nontrivial half depth ordinal).symm.trans readZero
 have physicalZero : Recurrence.physicalUpdated observation nontrivial half depth ordinal=0 :=
  actual_zero_physical (D.factory observation nontrivial half) (native observation nontrivial half depth ordinal) nativeZero
 exact Recurrence.original_updated_physical_nonzero observation nontrivial half depth ordinal physicalZero

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.ModelDecoder
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
