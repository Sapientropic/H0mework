import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
open private receipt_environment from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Source
open private native_input_word native_born_value from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source
namespace W
export NativeSigma.Writeback
 (retainedInNative bornValue bornWord nativeBoundary nativeInverseValue admissionValue)
end W
local instance recurrenceGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

def retained (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 W.retainedInNative factory (AS.bornAfterNative native) (W.bornValue native (W.nativeInverseValue native))

def OldAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 evaluation (R:=ℤ) (old factory native) (admittedBeta factory native)=retained factory native

/-- The next receipt's old coordinate is the entire inverse inherited from this actual birth. -/
theorem source_old
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket) :
 let actualFactory:=NativeSigma.Writeback.Input.withActualInput code factory
 OldAt actualFactory (AS.nativeAfterAdmission actualFactory packet) := by
 dsimp only
 let actualFactory:=NativeSigma.Writeback.Input.withActualInput code factory
 let native:=AS.nativeAfterAdmission actualFactory packet
 let born:=AS.bornAfterNative native
 let following:=AS.nativeAfterAdmission actualFactory born
 have input:=NativeSigma.Writeback.Input.born_after_native_input code native
  (NativeSigma.Writeback.Input.native_after_admission_input code factory packet)
 have generated:=native_input_word actualFactory born code input
  (W.bornWord native (W.nativeBoundary native))
 have environment:=receipt_environment following.2.1.1 (AS.stockCfg following.2.2.1)
 have oldRead : evaluation (R:=ℤ) (old actualFactory native) (admittedBeta actualFactory native)=
  evaluation (R:=ℤ) following.2.1.1.registered.input.environment (admittedBeta actualFactory native) :=
  congrArg (fun before=>evaluation (R:=ℤ) before (admittedBeta actualFactory native)) environment
 have source:=NativeSigma.Writeback.Dynamics.packet_next_active actualFactory packet
 have inverse:=native_born_value native
 exact oldRead.trans (generated.trans (congrArg (W.retainedInNative actualFactory born)
  ((congrArg (fun before=>evaluation (R:=ℤ) before
   (W.bornWord native (W.nativeBoundary native))) source).trans inverse)))

def PairAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 (residualEquivRange (updateInventory (R:=ℤ) (old factory native) (increment factory native))
  (canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native))
   (admittedBeta factory native))).val=
 (retained factory native,W.nativeInverseValue (nextNative factory native))

def UpdatedAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 (residualEquivRange
  (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
  (canonicalResidual
   (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
   (admittedBeta factory native))).val=
 retained factory native+W.nativeInverseValue (nextNative factory native)

private theorem pair_of_old (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (read : PairReadAt factory native) (inherited : OldAt factory native) : PairAt factory native :=
 read.trans (congrArg (fun value=>(value,W.nativeInverseValue (nextNative factory native))) inherited)

private theorem updated_of_old (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (read : UpdatedReadAt factory native) (inherited : OldAt factory native) : UpdatedAt factory native :=
 read.trans (congrArg (fun value : L.Value (PairValue C.Value) (nextNative factory native).1 ()=>
  value+W.nativeInverseValue (nextNative factory native)) inherited)

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem original_old : OldAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 source_old (FR.jointCode (RSource.code observation nontrivial half))
  (SF.defaultFactory (PairValue C.Value) C.Var ())
  (originalPredecessor observation nontrivial half depth (ordinal+1))

theorem original_pair_recurrence : PairAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 pair_of_old _ _ (original_pair observation nontrivial half depth ordinal)
  (original_old observation nontrivial half depth ordinal)

theorem original_updated_recurrence : UpdatedAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 updated_of_old _ _ (original_updated observation nontrivial half depth ordinal)
  (original_old observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
