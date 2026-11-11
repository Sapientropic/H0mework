import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Gram

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
open private collapse_native_shift from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Source
open private total from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Source
local instance updatedGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private theorem cast_roundtrip {α β : Type} (same : α=β) (value : β) :
 Eq.mp same (Eq.mp same.symm value)=value := by cases same; rfl

private theorem cast_add (grade nextGrade : Nat) (same : nextGrade=grade+1)
 (left right : L.Value (PairValue C.Value) nextGrade ()) :
 Eq.mp (congrArg (fun level=>L.Value (PairValue C.Value) level ()) same) (left+right)=
 Eq.mp (congrArg (fun level=>L.Value (PairValue C.Value) level ()) same) left+
 Eq.mp (congrArg (fun level=>L.Value (PairValue C.Value) level ()) same) right := by
 subst nextGrade
 rfl

private theorem collapse_native_add (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
 (left right : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :
 NativeSigma.collapseNative factory packet (left+right)=
 NativeSigma.collapseNative factory packet left+NativeSigma.collapseNative factory packet right :=
 (congrArg (CF.collapseValue packet.1)
  (cast_add packet.1 _ (AS.nativeAfterAdmission_grade factory packet) left right)).trans
  (OriginalKFiniteWard.collapse_add packet.1 _ _)

private def packetBranches (native : NativeSigma.NativePacket) :=
 CF.collapseValue native.1 (W.nativeInverseValue native,0)

private theorem retained_branches (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
 NativeSigma.collapseNative factory (AS.bornAfterNative native) (retained factory native)=packetBranches native := by
 let same:=congrArg (fun level=>L.Value (PairValue C.Value) level ())
  (AS.nativeAfterAdmission_grade factory (AS.bornAfterNative native))
 exact congrArg (CF.collapseValue native.1)
  (cast_roundtrip same (W.bornValue native (W.nativeInverseValue native),
   (0 : L.Value (PairValue C.Value) native.1 ())))

def actualUpdatedValue (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
 (residualEquivRange
  (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
  (canonicalResidual
   (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
   (admittedBeta factory native))).val

private theorem updated_branches_of_receipts
 (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
 (read : UpdatedAt factory native) :
 NativeSigma.collapseNative factory (AS.bornAfterNative native) (actualUpdatedValue factory native)=
 packetBranches native+packetBranches (nextNative factory native) := by
 let born:=AS.bornAfterNative native
 have update:=congrArg (NativeSigma.collapseNative factory born) read
 have split:=collapse_native_add factory born (retained factory native)
  (W.nativeInverseValue (nextNative factory native))
 have inherited:=congrArg₂ (fun left right=>left+right)
  (retained_branches factory native)
  (collapse_native_shift factory born (W.nativeInverseValue (nextNative factory native)))
 exact update.trans (split.trans inherited)

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def updatedBranches :=
 NativeSigma.collapseNative (D.factory observation nontrivial half)
  (AS.bornAfterNative (originalNative observation nontrivial half depth (ordinal+1)))
  (actualUpdatedValue (D.factory observation nontrivial half)
   (originalNative observation nontrivial half depth (ordinal+1)))

private theorem original_packet_branches (index : Nat) :
 packetBranches (originalNative observation nontrivial half depth index)=
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth index) :=
 (collapse_native_shift (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth index) _).symm.trans
  (actual_inverse_branches observation nontrivial half depth index)

private theorem following_packet_branches :
 packetBranches (nextNative (D.factory observation nontrivial half)
  (originalNative observation nontrivial half depth (ordinal+1)))=
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth (ordinal+2)) :=
 (congrArg packetBranches (Rooting.native_successor observation nontrivial half depth (ordinal+1))).symm.trans
  (original_packet_branches observation nontrivial half depth (ordinal+2))

/-- Both complete receipt contributions enter the actual following decoder before a physical sum. -/
theorem original_updated_four_R : updatedBranches observation nontrivial half depth ordinal=
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth (ordinal+1))+
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth (ordinal+2)) :=
 (updated_branches_of_receipts _ _ (original_updated_recurrence observation nontrivial half depth ordinal)).trans
  (congrArg₂ (fun left right=>left+right)
   (original_packet_branches observation nontrivial half depth (ordinal+1))
   (following_packet_branches observation nontrivial half depth ordinal))

private theorem total_add (left right : (BurnolPhysicalState.BurnolL2×BurnolPhysicalState.BurnolL2)×
 (BurnolPhysicalState.BurnolL2×BurnolPhysicalState.BurnolL2)) :
 total (left+right)=total left+total right := by
 unfold total
 simp only [Prod.fst_add,Prod.snd_add]
 abel

def physicalUpdated := total (updatedBranches observation nontrivial half depth ordinal)

/-- The updated beta retains its birth endpoint and the two actual source increments telescope. -/
theorem original_updated_total : physicalUpdated observation nontrivial half depth ordinal=
 D.raw observation nontrivial half depth (ordinal+3)-D.raw observation nontrivial half depth (ordinal+1) := by
 have branches:= (original_updated_four_R observation nontrivial half depth ordinal).trans
  (congrArg₂ (fun left right=>left+right)
   (actual_inverse_branches observation nontrivial half depth (ordinal+1)).symm
   (actual_inverse_branches observation nontrivial half depth (ordinal+2)).symm)
 have total : physicalUpdated observation nontrivial half depth ordinal=
  inverseTotal observation nontrivial half depth (ordinal+1)+inverseTotal observation nontrivial half depth (ordinal+2) :=
  (congrArg total branches).trans (total_add _ _)
 exact total.trans ((congrArg₂ (fun left right=>left+right)
  (actual_inverse_successor observation nontrivial half depth ordinal)
  (actual_inverse_successor observation nontrivial half depth (ordinal+1))).trans (by abel))

/-- Nonzero updated physical value is paid by the original square-fixed Gram consumer. -/
theorem original_updated_physical_nonzero : physicalUpdated observation nontrivial half depth ordinal≠0 := by
 intro zero
 have difference : D.raw observation nontrivial half depth (ordinal+3)-
  D.raw observation nontrivial half depth (ordinal+1)=0 :=
  (original_updated_total observation nontrivial half depth ordinal).symm.trans zero
 have twice : P.R observation nontrivial half (P.R observation nontrivial half
  (D.raw observation nontrivial half depth (ordinal+1)))=D.raw observation nontrivial half depth (ordinal+3) :=
  (congrArg (P.R observation nontrivial half) (D.raw_successor observation nontrivial half depth (ordinal+1)).symm).trans
   (D.raw_successor observation nontrivial half depth (ordinal+2)).symm
 exact Terminal.actual_raw_ne_zero observation nontrivial half depth (ordinal+1)
  (Gram.original_R_square_fixed_zero observation nontrivial half _ (twice.trans (sub_eq_zero.mp difference)))

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
