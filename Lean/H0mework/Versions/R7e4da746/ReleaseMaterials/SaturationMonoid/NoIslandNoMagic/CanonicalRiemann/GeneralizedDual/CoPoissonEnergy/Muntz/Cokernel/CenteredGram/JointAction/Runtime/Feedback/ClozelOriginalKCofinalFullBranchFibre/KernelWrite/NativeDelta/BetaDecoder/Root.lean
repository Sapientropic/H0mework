import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction.Continuation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Rooting
local instance rootGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (SourceOperationScalarInventoryLift.PairValue C.Value) grade target) :=
 L.groups (SourceOperationScalarInventoryLift.PairValue C.Value) grade
namespace Next
export BornInstalledJoint.MacroNext (nextNative)
end Next
def NativeNonzeroAt (native : NativeSigma.NativePacket) : Prop := NativeSigma.Writeback.nativeInverseValue native≠0

theorem inverse_transport {first second : NativeSigma.NativePacket} (same : first=second) :
 Eq.mp (congrArg (fun packet=>L.Value (SourceOperationScalarInventoryLift.PairValue C.Value) packet.1 ()) same)
  (NativeSigma.Writeback.nativeInverseValue first)=NativeSigma.Writeback.nativeInverseValue second := by
 cases same
 rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- Packet identity comes from the original family successor, retaining its entire source data. -/
theorem native_successor : originalNative observation nontrivial half depth (ordinal+1)=
 Next.nextNative observation nontrivial half depth ordinal :=
 congrArg (AS.nativeAfterAdmission (D.factory observation nontrivial half))
  (Admissions.packetAt_successor (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)

theorem next_inverse_nonzero : NativeNonzeroAt (Next.nextNative observation nontrivial half depth (ordinal+1)) := by
 rw [←native_successor observation nontrivial half depth (ordinal+1)]
 exact Terminal.actual_native_inverse_nonzero observation nontrivial half depth (ordinal+1)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Rooting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
