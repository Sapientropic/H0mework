import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Reader
export SourceGeneratedInquiryReceiptAction (actionReader actualMaterial afterEnvironment)
end Reader
namespace Input
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation (raw transported_action_raw actual_environment)
end Input
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next actualOccurrence)
end Shared
namespace Epoch
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Epoch
private theorem paired_environment_difference {Sorts : Type} {Value Var : Sorts → Type}
 [∀ target,AddCommGroup (Value target)] (after before : Env Value Var) :
 pairEnvironment after 0-pairEnvironment before 0 = pairEnvironment (after-before) 0 := by
 funext target name
 simp only [Pi.sub_apply,pairEnvironment,Prod.mk_sub_mk,sub_self]
 rfl

local instance materialSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

abbrev rSelected := actorSelected observation nontrivial half depth ordinal h H N
 (sourceRFactory observation nontrivial half producer) grade data sourceCfg language
abbrev rCfg := actorCfg observation nontrivial half depth ordinal h H N
 (sourceRFactory observation nontrivial half producer) grade data sourceCfg language
abbrev rBorn := actorBorn observation nontrivial half depth ordinal h H N
 (sourceRFactory observation nontrivial half producer) grade data sourceCfg language
abbrev rMaterial := Reader.actualMaterial
 (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
 (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)

/-- The actual reader uses the R AST installed before admission, on the supplied source occurrence. -/
theorem actual_material_reader_R
 (frame : SourceFrame grade sourceCfg)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 Reader.actionReader frame (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) supplied =
 Input.raw (grade+1) (Epoch.epoch frame) (language.symm ▸ FullR.sourceCode observation nontrivial half) supplied := by
 change Reader.actionReader frame (AS.stockCfg (AS.template (sourceRFactory observation nontrivial half producer)
  grade data sourceCfg language)) supplied = _
 unfold AS.template
 exact Input.transported_action_raw language producer (FullR.sourceCode observation nontrivial half) (grade+1) _ frame supplied

/-- Literal R execution and the actual material reader share Raw/Env; their query traces remain separate occurrences. -/
theorem actual_R_before_source_raw (frame : SourceFrame grade sourceCfg) :
 sourceRBeforeRaw (sourceRFactory observation nontrivial half producer) grade data sourceCfg language frame =
 Reader.actionReader frame (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
  (Shared.actualOccurrence frame) := rfl

private theorem settled_receipt_next {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 Shared.next (Complete.atReceipt cfg initial 0) cfg = Shared.nextBorn (Complete.atReceipt cfg initial 0) cfg := by
 have actual := (Complete.receipt cfg initial 0).2.2.2
 change (Complete.atReceipt cfg initial 0).action = Sum.inl (Complete.receipt cfg initial 0).2.1 at actual
 unfold Shared.next
 rw [actual]

theorem actual_R_environment (frame : SourceFrame grade sourceCfg) :
 (Reader.actionReader frame (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
  (Shared.actualOccurrence frame)).environment = pairEnvironment frame.activeEnvironment 0 := by
 have reader := actual_material_reader_R observation nontrivial half depth ordinal h H N producer grade data sourceCfg language frame (Shared.actualOccurrence frame)
 exact (congrArg (fun raw => raw.environment) reader).trans
  (congrArg (fun env => pairEnvironment env (0 : Env _ sourceCfg.LowVar)) (Input.actual_environment (grade+1) frame))

theorem actual_material_next : Shared.next
 (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
 (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) =
 rBorn observation nontrivial half depth ordinal h H N producer grade data sourceCfg language := settled_receipt_next _ _

theorem actual_material_after_environment : Reader.afterEnvironment
 (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
 (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) =
 pairEnvironment (rBorn observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment 0 := by
 unfold Reader.afterEnvironment
 rw [actual_material_next]
 exact actual_R_environment _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem actual_material_source_increment :
 (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).increment =
 pairEnvironment ((rBorn observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment-
  (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment) 0 := by
 change Reader.afterEnvironment _ _ - (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).environment = _
 rw [actual_material_after_environment]
 have before := actual_R_environment observation nontrivial half depth ordinal h H N producer grade data sourceCfg language
  (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
 change (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).environment = _ at before
 rw [before]
 exact paired_environment_difference _ _

/-- The actual calculation receipt keeps its own trace in the existing configured lowStock. -/
theorem actual_R_receipt_low_stock :
 SourceGeneratedInquiryReceiptAction.Configured.lowStock
  (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
  (rCfg observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) =
 SourceOperationPaidRelations.exposure
  (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).state.2 := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
