import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.FullResidual.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace D
export Lower.SourceFamily.Admissions (packetAt actual_index cofinal)
end D
namespace AS
export Lower.SourceFamily.ActivationSource (stockCfg)
end AS
variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}
local instance levelGroups (n : Nat) (target : Sorts) : AddCommGroup (L.Value (PairValue V) n target) :=
  L.groups (PairValue V) n target
variable (sourceCode : Expr (PairValue V) X s) (baseFactory : SF.Factory (PairValue V) X s)
variable (n : Nat) (seed : SF.Seed (PairValue V) X s n)
variable (frame : A.M.Frame (Value := L.Value (PairValue V) n) (Var := X) (sort := s))
abbrev configuration := SF.cfg (factory sourceCode baseFactory) n seed

def sourceInput : Env (PairValue (PairValue V)) X :=
  fun target name => CF.collapseValue n (frame.activeEnvironment target name, 0)

theorem actual_branches :
    CF.collapseValue n (R.actionResultAt frame (configuration sourceCode baseFactory n seed)
      (S.actualOccurrence frame)).2.2.1 =
        (sourceCode.eval (physicalInput (completeInput (sourceInput n frame))),
         sourceCode.effect (physicalInput (completeInput (sourceInput n frame)))
           (residualInput (completeInput (sourceInput n frame)))) :=
  (AI.actual_base_value n frame (jointCode sourceCode) baseFactory seed).trans
    (joint_eval sourceCode (sourceInput n frame))

theorem actual_complete :
    let generated := CF.collapseValue n (R.actionResultAt frame (configuration sourceCode baseFactory n seed)
      (S.actualOccurrence frame)).2.2.1
    generated.1 + generated.2 =
      sourceCode.eval (physicalInput (completeInput (sourceInput n frame)) +
        residualInput (completeInput (sourceInput n frame))) :=
  (congrArg (fun pair : PairValue (PairValue V) s => pair.1 + pair.2)
    (actual_branches sourceCode baseFactory n seed frame)).trans (Expr.eval_update _ _ _).symm

theorem actual_trace : (R.actualMaterial frame (configuration sourceCode baseFactory n seed)).state.2.length =
    remaining (CF.codeAt (jointCode sourceCode) n) :=
  AI.actual_trace n frame (jointCode sourceCode) baseFactory seed

theorem updated_branches (write : PairValue (L.Value (PairValue V) n) s →
    Env (PairValue (L.Value (PairValue V) n)) X) :
    CF.collapseValue n
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.oldPaid frame (configuration sourceCode baseFactory n seed) +
        SourceGeneratedInquiryReceiptAction.Configured.Writeback.nativeValue frame
          (configuration sourceCode baseFactory n seed) write) =
      (sourceCode.eval (physicalInput (completeInput (sourceInput n (S.next frame (configuration sourceCode baseFactory n seed))))),
       sourceCode.effect (physicalInput (completeInput (sourceInput n (S.next frame (configuration sourceCode baseFactory n seed)))))
         (residualInput (completeInput (sourceInput n (S.next frame (configuration sourceCode baseFactory n seed)))))) :=
  (AI.updated_base_total n frame (jointCode sourceCode) baseFactory seed write).trans
    (joint_eval sourceCode _)

theorem born_branches {W Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (W target)]
    (baseFactory : SF.Factory (PairValue W) Y PUnit.unit) (grade : Nat)
    (packet : SF.Packet (W := PairValue W) (X := Y) (s := PUnit.unit) grade)
    (baseCfg : A.Programme (PhysicalValue := L.Value (PairValue W) grade) (PhysicalVar := Y) (sort := PUnit.unit))
    (sameVar : baseCfg.LowVar = Y) (sourceCode : Expr (PairValue W) baseCfg.LowVar PUnit.unit)
    (active : Env (L.Value (PairValue W) grade) baseCfg.LowVar)
    (literal : (R.actualMaterial packet.1 baseCfg).raw = CF.codeAt (jointCode sourceCode) grade)
    (updated : (N.input (R.actualMaterial packet.1 baseCfg)).environment = pairEnvironment active 0)
    (name : baseCfg.LowVar PUnit.unit) :
    let actualInput := fun target slot => CF.collapseValue grade (active target slot, 0)
    CF.collapseValue grade ((SS.born baseFactory grade packet baseCfg sameVar).activeEnvironment PUnit.unit name) =
      (sourceCode.eval (physicalInput (completeInput actualInput)),
       sourceCode.effect (physicalInput (completeInput actualInput)) (residualInput (completeInput actualInput))) :=
  (AI.successor_born_base (V := PairValue W) (Y := Y) baseFactory grade packet baseCfg sameVar
    (jointCode sourceCode) active literal updated name).trans (joint_eval sourceCode _)

theorem born_at_seed {W Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (W target)]
    (sourceCode : Expr (PairValue W) Y PUnit.unit) (baseFactory : SF.Factory (PairValue W) Y PUnit.unit)
    (sourceFrame : A.M.Frame (Value := PairValue W) (Var := Y) (sort := PUnit.unit))
    (inventory : SF.Seed (PairValue W) Y PUnit.unit 0)
    (keepNext : (S.next sourceFrame (SF.cfg (factory sourceCode baseFactory) 0 inventory)).activeEnvironment =
      sourceFrame.activeEnvironment) (name : Y PUnit.unit) :
    (SS.born (factory sourceCode baseFactory) 0 (sourceFrame, inventory)
      (SF.cfg (factory sourceCode baseFactory) 0 inventory) rfl).activeEnvironment PUnit.unit name =
        (sourceCode.eval (physicalInput sourceFrame.activeEnvironment),
          sourceCode.effect (physicalInput sourceFrame.activeEnvironment) (residualInput sourceFrame.activeEnvironment)) := by
  have updated := (Lower.SourceFamily.ActualInputCalculation.updated_environment
    (W := PairValue W) (X := Y) 0 sourceFrame (jointCode sourceCode) baseFactory inventory).trans
      (congrArg (fun env => pairEnvironment env (0 : Env (PairValue W) Y)) keepNext)
  have bornValue := born_branches (W := W) (Y := Y) (factory sourceCode baseFactory) 0
    (sourceFrame, inventory) (SF.cfg (factory sourceCode baseFactory) 0 inventory) rfl
    sourceCode sourceFrame.activeEnvironment rfl updated name
  have input : completeInput (fun target slot => CF.collapseValue (W := PairValue W) 0
    (sourceFrame.activeEnvironment target slot, 0)) = sourceFrame.activeEnvironment := by
    funext target slot
    exact add_zero _
  exact bornValue.trans (congrArg (fun environment =>
    (sourceCode.eval (physicalInput environment), sourceCode.effect (physicalInput environment) (residualInput environment))) input)

variable (initial : A.M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s))
variable (language : firstCfg.LowVar = X)

theorem cofinal_branches (ordinal : Nat) :
    let packet := D.packetAt (factory sourceCode baseFactory) initial firstCfg language (ordinal + 1)
    let rawInput := fun target name => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name, 0)
    CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 (AS.stockCfg packet.2.2.1)
      (S.actualOccurrence packet.2.1.1)).2.2.1 =
      (sourceCode.eval (physicalInput (completeInput rawInput)),
       sourceCode.effect (physicalInput (completeInput rawInput)) (residualInput (completeInput rawInput))) :=
  (AI.cofinal_actual_value (jointCode sourceCode) baseFactory initial firstCfg language ordinal).trans
    (joint_eval sourceCode _)

theorem cofinal_complete (ordinal : Nat) :
    let packet := D.packetAt (factory sourceCode baseFactory) initial firstCfg language (ordinal + 1)
    let rawInput := fun target name => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name, 0)
    let generated := CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 (AS.stockCfg packet.2.2.1)
      (S.actualOccurrence packet.2.1.1)).2.2.1
    generated.1 + generated.2 = sourceCode.eval (physicalInput (completeInput rawInput) + residualInput (completeInput rawInput)) :=
  (congrArg (fun pair : PairValue (PairValue V) s => pair.1 + pair.2)
    (cofinal_branches sourceCode baseFactory initial firstCfg language ordinal)).trans (Expr.eval_update _ _ _).symm

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
