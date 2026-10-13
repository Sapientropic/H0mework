import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.Source
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local instance] levelGroups
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue updated_total)
end WB
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (stockCfg nextCfg next_action_reader nextSeed stock_action_reader AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (packetAt packetAt_successor actual_index cofinal)
end D
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (nextCfg template seed reader_preserved calculation_reader_preserved oldPair nativeValue updated_total born born_environment)
end SS
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
variable (n : Nat) (frame : A.M.Frame (Value := L.Value W n) (Var := X) (sort := s))
variable (sourceCode : Expr (PairValue W) X s) (factory : SF.Factory W X s) (seed : SF.Seed W X s n)
abbrev configuration := SF.cfg (withActualInput sourceCode factory) n seed

theorem actual_value :
    (R.actionResultAt frame (configuration n sourceCode factory seed) (S.actualOccurrence frame)).2.2.1 =
      (CF.codeAt sourceCode n).eval (pairEnvironment frame.activeEnvironment 0) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot frame (configuration n sourceCode factory seed)).toAuthoritativeRoot
    (R.actionReader frame (configuration n sourceCode factory seed)) (S.actualOccurrence frame)).trans
      (congrArg (fun env => (CF.codeAt sourceCode n).eval env)
        (actual_reader_environment n frame sourceCode factory seed))

theorem actual_trace : (R.actualMaterial frame (configuration n sourceCode factory seed)).state.2.length =
    remaining (CF.codeAt sourceCode n) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (S.baseRoot frame (configuration n sourceCode factory seed)).toAuthoritativeRoot
    (R.actionReader frame (configuration n sourceCode factory seed)) (S.actualOccurrence frame)

theorem actual_base_value :
    CF.collapseValue n (R.actionResultAt frame (configuration n sourceCode factory seed) (S.actualOccurrence frame)).2.2.1 =
      sourceCode.eval (fun target name => CF.collapseValue n (frame.activeEnvironment target name, 0)) :=
  (congrArg (CF.collapseValue n) (actual_value n frame sourceCode factory seed)).trans
    (CF.code_base_value sourceCode n (pairEnvironment frame.activeEnvironment 0))

theorem updated_environment :
    (N.input (R.actualMaterial frame (configuration n sourceCode factory seed))).environment =
      pairEnvironment (S.next frame (configuration n sourceCode factory seed)).activeEnvironment 0 :=
  (add_sub_cancel (R.actualMaterial frame (configuration n sourceCode factory seed)).environment
    (R.afterEnvironment frame (configuration n sourceCode factory seed))).trans
      (actual_reader_environment n (S.next frame (configuration n sourceCode factory seed)) sourceCode factory seed)

theorem updated_total (write : PairValue (L.Value W n) s → Env (PairValue (L.Value W n)) X) :
    WB.oldPaid frame (configuration n sourceCode factory seed) +
      WB.nativeValue frame (configuration n sourceCode factory seed) write =
        (CF.codeAt sourceCode n).eval
          (pairEnvironment (S.next frame (configuration n sourceCode factory seed)).activeEnvironment 0) :=
  (WB.updated_total frame (configuration n sourceCode factory seed) write).trans
    (congrArg (fun env => (CF.codeAt sourceCode n).eval env) (updated_environment n frame sourceCode factory seed))

theorem updated_base_total (write : PairValue (L.Value W n) s → Env (PairValue (L.Value W n)) X) :
    CF.collapseValue n (WB.oldPaid frame (configuration n sourceCode factory seed) +
      WB.nativeValue frame (configuration n sourceCode factory seed) write) =
        sourceCode.eval (fun target name => CF.collapseValue n
          ((S.next frame (configuration n sourceCode factory seed)).activeEnvironment target name, 0)) :=
  (congrArg (CF.collapseValue n) (updated_total n frame sourceCode factory seed write)).trans
    (CF.code_base_value sourceCode n _)

variable (data : SF.Packet (W := W) (X := X) (s := s) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X)
variable (currentFrame : A.M.Frame (Value := PairValue (L.Value W n)) (Var := sourceCfg.LowVar) (sort := s))

theorem next_action_raw {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current := current)) :
    R.actionReader currentFrame (AS.nextCfg (withActualInput sourceCode factory) n data sourceCfg language) supplied =
      raw (n + 1) (A.epoch currentFrame) (language.symm ▸ sourceCode) supplied := by
  rw [AS.next_action_reader]
  exact transported_action_raw language factory sourceCode (n + 1)
    (AS.nextSeed (withActualInput sourceCode factory) n data sourceCfg language) currentFrame supplied

theorem successor_action_raw {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (baseCode : Expr (PairValue V) Y PUnit.unit) (baseFactory : SF.Factory V Y PUnit.unit)
    (grade : Nat) (packet : SF.Packet (W := V) (X := Y) (s := PUnit.unit) grade)
    (baseCfg : A.Programme (PhysicalValue := L.Value V grade) (PhysicalVar := Y) (sort := PUnit.unit))
    (sameVar : baseCfg.LowVar = Y)
    (nextFrame : A.M.Frame (Value := PairValue (L.Value V grade)) (Var := baseCfg.LowVar) (sort := PUnit.unit))
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current nextFrame.registered}
    (supplied : I.Occurrence nextFrame (current := current)) :
    R.actionReader nextFrame (SS.nextCfg (withActualInput baseCode baseFactory) grade packet baseCfg sameVar) supplied =
      raw (grade + 1) (A.epoch nextFrame) (sameVar.symm ▸ baseCode) supplied := by
  change R.actionReader nextFrame (SS.template (withActualInput baseCode baseFactory) grade packet baseCfg sameVar) supplied = _
  exact transported_action_raw sameVar baseFactory baseCode (grade + 1)
    (SS.seed (withActualInput baseCode baseFactory) grade packet baseCfg sameVar) nextFrame supplied

theorem successor_updated_environment {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (baseCode : Expr (PairValue V) Y PUnit.unit) (baseFactory : SF.Factory V Y PUnit.unit)
    (grade : Nat) (packet : SF.Packet (W := V) (X := Y) (s := PUnit.unit) grade)
    (baseCfg : A.Programme (PhysicalValue := L.Value V grade) (PhysicalVar := Y) (sort := PUnit.unit))
    (sameVar : baseCfg.LowVar = Y)
    (nextFrame : A.M.Frame (Value := PairValue (L.Value V grade)) (Var := baseCfg.LowVar) (sort := PUnit.unit)) :
    let nextCfg := SS.nextCfg (withActualInput baseCode baseFactory) grade packet baseCfg sameVar
    (N.input (R.actualMaterial nextFrame nextCfg)).environment =
      pairEnvironment (S.next nextFrame nextCfg).activeEnvironment 0 := by
  let nextCfg := SS.nextCfg (withActualInput baseCode baseFactory) grade packet baseCfg sameVar
  have rawEq := successor_action_raw baseCode baseFactory grade packet baseCfg sameVar
    (S.next nextFrame nextCfg) (S.actualOccurrence (S.next nextFrame nextCfg))
  exact (add_sub_cancel (R.actualMaterial nextFrame nextCfg).environment (R.afterEnvironment nextFrame nextCfg)).trans
    ((congrArg (fun sourceRaw : O.Raw (Value := PairValue (PairValue (L.Value V grade)))
      (Var := baseCfg.LowVar) (sort := PUnit.unit) => sourceRaw.environment) rawEq).trans
        (congrArg (fun env => pairEnvironment env (0 : Env (PairValue (L.Value V grade)) baseCfg.LowVar))
          (actual_environment (W := V) (X := baseCfg.LowVar) (grade + 1) (S.next nextFrame nextCfg))))

theorem successor_feedback_base {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (baseFactory : SF.Factory V Y PUnit.unit) (grade : Nat)
    (packet : SF.Packet (W := V) (X := Y) (s := PUnit.unit) grade)
    (baseCfg : A.Programme (PhysicalValue := L.Value V grade) (PhysicalVar := Y) (sort := PUnit.unit))
    (sameVar : baseCfg.LowVar = Y) (baseCode : Expr (PairValue V) baseCfg.LowVar PUnit.unit)
    (active : Env (L.Value V grade) baseCfg.LowVar)
    (literal : (R.actualMaterial packet.1 baseCfg).raw = CF.codeAt baseCode grade)
    (updated : (N.input (R.actualMaterial packet.1 baseCfg)).environment = pairEnvironment active 0) :
    CF.collapseValue grade (SS.oldPair grade packet baseCfg + SS.nativeValue baseFactory grade packet baseCfg sameVar) =
      baseCode.eval (fun target name => CF.collapseValue grade (active target name, 0)) := by
  have total := SS.updated_total baseFactory grade packet baseCfg sameVar
  have generated := total.trans ((congrArg (fun expression => expression.eval
    (N.input (R.actualMaterial packet.1 baseCfg)).environment) literal).trans
      (congrArg (fun env => (CF.codeAt baseCode grade).eval env) updated))
  exact (congrArg (CF.collapseValue grade) generated).trans
    (CF.code_base_value baseCode grade (pairEnvironment active 0))

theorem successor_born_base {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (baseFactory : SF.Factory V Y PUnit.unit) (grade : Nat)
    (packet : SF.Packet (W := V) (X := Y) (s := PUnit.unit) grade)
    (baseCfg : A.Programme (PhysicalValue := L.Value V grade) (PhysicalVar := Y) (sort := PUnit.unit))
    (sameVar : baseCfg.LowVar = Y) (baseCode : Expr (PairValue V) baseCfg.LowVar PUnit.unit)
    (active : Env (L.Value V grade) baseCfg.LowVar)
    (literal : (R.actualMaterial packet.1 baseCfg).raw = CF.codeAt baseCode grade)
    (updated : (N.input (R.actualMaterial packet.1 baseCfg)).environment = pairEnvironment active 0)
    (name : baseCfg.LowVar PUnit.unit) :
    CF.collapseValue grade ((SS.born baseFactory grade packet baseCfg sameVar).activeEnvironment PUnit.unit name) =
      baseCode.eval (fun target slotName => CF.collapseValue grade (active target slotName, 0)) :=
  (congrArg (fun env => CF.collapseValue grade (env PUnit.unit name))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
      (SS.born_environment baseFactory grade packet baseCfg sameVar))).trans
        (successor_feedback_base baseFactory grade packet baseCfg sameVar baseCode active literal updated)

def HasActualInput (grade : Nat)
    (programme : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := s))
    (sameVar : programme.LowVar = X) : Prop :=
  ∀ (currentFrame : A.M.Frame (Value := L.Value W grade) (Var := X) (sort := s))
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current := current)),
    R.actionReader currentFrame (AS.stockCfg programme) supplied =
      Eq.mp (congrArg (fun variableFamily => O.Raw (Value := PairValue (L.Value W grade)) (Var := variableFamily) (sort := s))
        sameVar.symm) (raw grade (A.epoch currentFrame) sourceCode supplied)

theorem native_after_admission_input (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
    HasActualInput sourceCode (AS.nativeAfterAdmission (withActualInput sourceCode factory) packet).1
      (AS.nativeAfterAdmission (withActualInput sourceCode factory) packet).2.2.1
      (AS.nativeAfterAdmission (withActualInput sourceCode factory) packet).2.2.2.down := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    intro nextFrame current supplied
    exact next_action_raw grade sourceCode factory packetData
      ⟨X, datum, inventory, pairInventory⟩ rfl nextFrame supplied

theorem born_after_native_input (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
    (generated : HasActualInput sourceCode packet.1 packet.2.2.1 packet.2.2.2.down) :
    HasActualInput sourceCode (AS.bornAfterNative packet).1 (AS.bornAfterNative packet).2.2.1
      (AS.bornAfterNative packet).2.2.2.down := by
  intro nextFrame current supplied
  exact (AS.stock_action_reader nextFrame (AS.stockCfg packet.2.2.1) supplied).trans
    (generated nextFrame supplied)

variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (firstLanguage : firstCfg.LowVar = X)

theorem next_after_born
    (previous : A.M.Frame (Value := L.Value W n) (Var := X) (sort := s))
    (previousCfg activeCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s)) :
    S.next (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn previous previousCfg) activeCfg =
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn previous previousCfg).mathNext := by
  let born := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn previous previousCfg
  unfold S.next
  cases actual : born.action with
  | inr paid => rfl
  | inl settled =>
    have zero := (RootGeneratedDebtActivationJointSource.Idle.law born.registered.input.environment
      born.registered.input.expression).settlement_budget_zero settled
    have budget := SourceRegisteredClaimClock.remainder_generated born
    have growth := previous.request_budget
    change remaining born.event.state.1 = 0 at zero
    change remaining born.event.state.1 = remaining previous.request.input.expression - (0 + 1) at budget
    omega

theorem cofinal_actual_input (ordinal : Nat) :
    let packet := D.packetAt (withActualInput sourceCode factory) initial firstCfg firstLanguage (ordinal + 1)
    HasActualInput sourceCode packet.1 packet.2.2.1 packet.2.2.2.down := by
  dsimp only
  rw [D.packetAt_successor]
  exact born_after_native_input sourceCode _ (native_after_admission_input sourceCode factory _)

theorem cofinal_actual_value (ordinal : Nat) :
    let packet := D.packetAt (withActualInput sourceCode factory) initial firstCfg firstLanguage (ordinal + 1)
    CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 (AS.stockCfg packet.2.2.1)
      (S.actualOccurrence packet.2.1.1)).2.2.1 =
        sourceCode.eval (fun target name => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name, 0)) := by
  have generated := cofinal_actual_input sourceCode factory initial firstCfg firstLanguage ordinal
  generalize packetEq : D.packetAt (withActualInput sourceCode factory) initial firstCfg firstLanguage (ordinal + 1) = packet at generated ⊢
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := s) :=
      AS.stockCfg ⟨X, datum, inventory, pairInventory⟩
    let actual := S.actualOccurrence packetData.1
    let seen := R.actionReader packetData.1 cfg actual
    have readerEq : seen = raw grade (A.epoch packetData.1) sourceCode actual := generated packetData.1 actual
    have paid : (R.actionResultAt packetData.1 cfg actual).2.2.1 = seen.expression.eval seen.environment :=
      RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
        (S.baseRoot packetData.1 cfg).toAuthoritativeRoot (R.actionReader packetData.1 cfg) actual
    have value : (R.actionResultAt packetData.1 cfg actual).2.2.1 =
        (CF.codeAt sourceCode grade).eval (pairEnvironment packetData.1.activeEnvironment 0) :=
      (paid.trans (congrArg (fun sourceRaw : O.Raw (Value := PairValue (L.Value W grade)) (Var := X) (sort := s) =>
        sourceRaw.expression.eval sourceRaw.environment) readerEq)).trans
          (congrArg (fun env => (CF.codeAt sourceCode grade).eval (pairEnvironment env (0 : Env (L.Value W grade) X)))
            (actual_environment grade packetData.1))
    exact (congrArg (CF.collapseValue grade) value).trans (CF.code_base_value sourceCode grade _)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
