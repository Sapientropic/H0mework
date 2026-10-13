import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Future.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction.Future
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (scalar pair receiver nextSeed nextBase template stockCfg write)
end AS
variable {Sorts : Type u} (W X : Sorts → Type u) [∀ t, AddCommGroup (W t)] (slot : Sorts)
local instance seedFamilyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X slot) (sourceSeed suppliedSeed : SF.Seed W X slot 0)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value := W) (Var := X) (sort := slot))
variable (sourceCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := slot))
variable (language : sourceCfg.LowVar = X)

theorem first_source_cfg :
 SF.cfg (fromSourceSeed W X slot factory sourceSeed) 0 suppliedSeed = SF.cfg factory 0 sourceSeed := rfl

theorem first_source_scalar :
 AS.scalar (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
 AS.scalar factory 0 (frame,sourceSeed) sourceCfg language := rfl

theorem first_source_pair :
 AS.pair (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
 AS.pair factory 0 (frame,sourceSeed) sourceCfg language := rfl

theorem first_source_receiver :
 AS.receiver (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
 AS.receiver factory 0 (frame,sourceSeed) sourceCfg language := rfl

theorem first_source_next_seed :
 AS.nextSeed (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
 AS.nextSeed factory 0 (frame,sourceSeed) sourceCfg language := rfl

theorem first_source_next_base :
 AS.nextBase (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
 AS.nextBase factory 0 (frame,sourceSeed) sourceCfg language := by
 have shifted : (language.symm ▸ fromSourceSeed W X slot factory sourceSeed : SF.Factory W sourceCfg.LowVar slot).datum 1 =
   (language.symm ▸ factory : SF.Factory W sourceCfg.LowVar slot).datum 1 := by
  generalize sourceCfg.LowVar = Y at language ⊢
  cases language
  rfl
 have shiftedScalar : (language.symm ▸ fromSourceSeed W X slot factory sourceSeed : SF.Factory W sourceCfg.LowVar slot).nextInventory 1 =
   (language.symm ▸ factory : SF.Factory W sourceCfg.LowVar slot).nextInventory 1 := by
  generalize sourceCfg.LowVar = Y at language ⊢
  cases language
  rfl
 have shiftedPair : (language.symm ▸ fromSourceSeed W X slot factory sourceSeed : SF.Factory W sourceCfg.LowVar slot).nextPairInventory 1 =
   (language.symm ▸ factory : SF.Factory W sourceCfg.LowVar slot).nextPairInventory 1 := by
  generalize sourceCfg.LowVar = Y at language ⊢
  cases language
  rfl
 have sourceWrite : AS.write (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
  AS.write factory 0 (frame,sourceSeed) sourceCfg language := by
  funext value target name
  unfold AS.write
  simp only [first_source_receiver]
 have sourceTemplate : AS.template (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language =
  AS.template factory 0 (frame,sourceSeed) sourceCfg language := by
  unfold AS.template SF.cfg
  simp only [first_source_next_seed, shifted, shiftedScalar, shiftedPair]
 unfold AS.nextBase
 rw [sourceTemplate]
 change (fun write => { AS.template factory 0 (frame,sourceSeed) sourceCfg language with
  datum := fun nextFrame => { (AS.template factory 0 (frame,sourceSeed) sourceCfg language).datum nextFrame with
   nextEnvironmentReadAt := ((SourceGeneratedInquiryReceiptAction.Configured.Writeback.programme frame sourceCfg write).datum nextFrame).nextEnvironmentReadAt } })
  (AS.write (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language) = _
 exact congrArg (fun write : PairValue W slot → Env (PairValue W) sourceCfg.LowVar =>
  { AS.template factory 0 (frame,sourceSeed) sourceCfg language with
   datum := fun nextFrame => { (AS.template factory 0 (frame,sourceSeed) sourceCfg language).datum nextFrame with
    nextEnvironmentReadAt := ((SourceGeneratedInquiryReceiptAction.Configured.Writeback.programme frame sourceCfg write).datum nextFrame).nextEnvironmentReadAt } }) sourceWrite

/-- The generated receiver and successor history use the explicit source seed, even with an unrelated auxiliary seed. -/
theorem source_seed_successor :
 (AS.receiver (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language,
  AS.nextSeed (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language,
  AS.nextBase (fromSourceSeed W X slot factory sourceSeed) 0 (frame,suppliedSeed) sourceCfg language) =
 (AS.receiver factory 0 (frame,sourceSeed) sourceCfg language,
  AS.nextSeed factory 0 (frame,sourceSeed) sourceCfg language,
  AS.nextBase factory 0 (frame,sourceSeed) sourceCfg language) := by
 rw [first_source_receiver, first_source_next_seed, first_source_next_base]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
