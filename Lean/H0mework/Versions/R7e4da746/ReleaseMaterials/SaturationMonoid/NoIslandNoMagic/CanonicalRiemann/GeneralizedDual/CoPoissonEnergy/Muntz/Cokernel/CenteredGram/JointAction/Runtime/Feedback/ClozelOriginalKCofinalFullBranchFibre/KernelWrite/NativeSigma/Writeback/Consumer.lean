import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Disposition

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open private native_sigma_next_evaluator from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source
local instance rootConsumerGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private theorem retained_pair_zero (factory : NativeFactory) (packet : NativePacket)
 (value : L.Value (PairValue C.Value) packet.1 ()) :
 retainedPair factory packet value=0 ↔ value=0 := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  change ((value,0),0)=0 ↔ value=0
  constructor
  · intro zero; exact congrArg (fun entry=>entry.1.1) zero
  · intro zero; cases zero; rfl

private theorem born_value_zero (native : NativePacket) (value : L.Value (PairValue C.Value) native.1 ()) :
 bornValue native value=0 ↔ value=0 := Iff.rfl

private theorem sound_receipt_zero (native : NativePacket)
 (word : Formal ℤ (PairValue (L.Value (PairValue C.Value) native.1)) C.Var ())
 (belongs : word∈(nativeHistory native).relationClosure)
 (sound : GeneratedRelationSoundnessAt (nativeFace native)) : nativeEvaluation native word=0 :=
 LinearMap.mem_ker.mp (sound.sound belongs)

/-- Eliminate the existing phase, retaining its actual realization or selected residual payload. -/
def ReceiptAt (native : NativePacket) (constraint : Prop)
 (phase : ResidualDispositionOutcome (nativeFace native)) : Type :=
 match phase with
 | .faithful _ _ realization => PLift constraint × (type_of% realization)
 | .unsound obstruction coordinate => PLift (type_of% obstruction) × (type_of% coordinate)
 | .kernelResidual _ obstruction coordinate =>
    PLift constraint × PLift (type_of% obstruction) × (type_of% coordinate)
 | .coverageResidual _ obstruction coordinate =>
    PLift constraint × PLift (type_of% obstruction) × (type_of% coordinate)

private def consume_phase (native : NativePacket) (constraint : Prop)
 (fromSource : ∀ _sound : GeneratedRelationSoundnessAt (nativeFace native),constraint)
 (phase : ResidualDispositionOutcome (nativeFace native)) : ReceiptAt native constraint phase :=
 match phase with
 | .faithful sound _ realization => ⟨⟨fromSource sound⟩,realization⟩
 | .unsound obstruction coordinate => ⟨⟨obstruction⟩,coordinate⟩
 | .kernelResidual sound obstruction coordinate => ⟨⟨fromSource sound⟩,⟨obstruction⟩,coordinate⟩
 | .coverageResidual sound obstruction coordinate => ⟨⟨fromSource sound⟩,⟨obstruction⟩,coordinate⟩

private theorem generated_sound_inverse_zero
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (factory : NativeFactory) (packet : NativePacket) (positive : 0 < remaining code) :
 let actualFactory:=Input.withActualInput code factory
 let native:=AS.nativeAfterAdmission actualFactory packet
 let born:=AS.bornAfterNative native
 let next:=AS.nativeAfterAdmission actualFactory born
 nativeReceiptTransfer actualFactory native (nativeBoundary native)∈(nativeHistory next).relationClosure →
 GeneratedRelationSoundnessAt (nativeFace next)→nativeInverseValue native=0 := by
 dsimp only
 let actualFactory:=Input.withActualInput code factory
 let native:=AS.nativeAfterAdmission actualFactory packet
 let born:=AS.bornAfterNative native
 let next:=AS.nativeAfterAdmission actualFactory born
 intro member sound
 have zero:=sound_receipt_zero next _ member sound
 have source:=native_sigma_next_evaluator code factory packet positive
 have retained:=source.symm.trans zero
 have valueZero:=(retained_pair_zero actualFactory born _).mp retained
 exact (born_value_zero native _).mp valueZero

private def generatedRootConsumer
 (actualFactory : NativeFactory) (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (factory : NativeFactory) (packet native next : NativePacket)
 (actual : native=AS.nativeAfterAdmission actualFactory packet)
 (nextActual : next=AS.nativeAfterAdmission actualFactory (AS.bornAfterNative native))
 (generated : actualFactory=Input.withActualInput code factory) (positive : 0 < remaining code) :
 nativeReceiptTransfer actualFactory native (nativeBoundary native)∈
  (nativeHistory (AS.nativeAfterAdmission actualFactory (AS.bornAfterNative native))).relationClosure →
 (phase : ResidualDispositionOutcome (nativeFace next))→
 ReceiptAt next (nativeInverseValue native=0) phase := by
 subst next
 subst native
 subst actualFactory
 intro member phase
 exact consume_phase _ _ (generated_sound_inverse_zero code factory packet positive member) phase

private def installed_phase_at_native
 (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (factory : NativeFactory)
 (generated : factory=Input.withActualInput code (SF.defaultFactory (PairValue C.Value) C.Var ()))
 (packet native : NativePacket) (actual : native=AS.nativeAfterAdmission factory packet) :
 ResidualDispositionOutcome (nativeFace native) := by
 subst native
 exact BornInstalledJoint.actualPhase code factory generated packet (AS.nativeAfterAdmission factory packet).2.1.1

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The same full receipt is consumed by the root's actual next phase; no phase is supplied by the caller. -/
def original_sigma_root_consumer :=
 generatedRootConsumer (D.factory observation nontrivial half)
  (FR.jointCode (RSource.code observation nontrivial half))
  (SF.defaultFactory (PairValue C.Value) C.Var ())
  (originalPredecessor observation nontrivial half depth ordinal)
  (originalNative observation nontrivial half depth ordinal)
  (Next.nextNative observation nontrivial half depth ordinal) rfl rfl rfl (by change 0<4; omega)
  (original_sigma_next_relation observation nontrivial half depth ordinal)
  (installed_phase_at_native (FR.jointCode (RSource.code observation nontrivial half))
   (D.factory observation nontrivial half) rfl (Next.bornPacket observation nontrivial half depth ordinal)
   (Next.nextNative observation nontrivial half depth ordinal) rfl)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
