import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Factory.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local instance] levelGroups
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue updated_total native_effect native_inverse)
end WB
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (stockCfg nextCfg next_action_reader receiver nextSeed AdmissionPacket nativeAfterAdmission bornAfterNative stock_action_reader)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (packetAt packetAt_successor actual_index index historyAt history_end_index cofinal)
end D
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
variable (factory : SF.Factory W X s) (sourceCode : Expr (PairValue W) X s)
variable (n : Nat) (seed : SF.Seed W X s n)
variable (frame : A.M.Frame (Value := L.Value W n) (Var := X) (sort := s))

abbrev configuration := SF.cfg (withCalculation factory sourceCode) n seed

theorem actual_source_code : (R.actualMaterial frame (configuration factory sourceCode n seed)).raw = codeAt sourceCode n := rfl

theorem actual_source_environment : (R.actualMaterial frame (configuration factory sourceCode n seed)).environment =
    ((factory.datum n seed (A.epoch frame)).reader (S.actualOccurrence frame)).environment := rfl

theorem actual_value {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    (R.actionResultAt frame (configuration factory sourceCode n seed) supplied).2.2.1 =
      (codeAt sourceCode n).eval (((factory.datum n seed (A.epoch frame)).reader supplied).environment) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot frame (configuration factory sourceCode n seed)).toAuthoritativeRoot
    (R.actionReader frame (configuration factory sourceCode n seed)) supplied

theorem actual_trace : (R.actualMaterial frame (configuration factory sourceCode n seed)).state.2.length =
    remaining (codeAt sourceCode n) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (S.baseRoot frame (configuration factory sourceCode n seed)).toAuthoritativeRoot
    (R.actionReader frame (configuration factory sourceCode n seed)) (S.actualOccurrence frame)

theorem actual_updated_total
    (write : PairValue (L.Value W n) s → Env (PairValue (L.Value W n)) X) :
    WB.oldPaid frame (configuration factory sourceCode n seed) +
      WB.nativeValue frame (configuration factory sourceCode n seed) write =
        (codeAt sourceCode n).eval (N.input (R.actualMaterial frame (configuration factory sourceCode n seed))).environment :=
  WB.updated_total frame (configuration factory sourceCode n seed) write

theorem next_code_value (environment increment : Env (PairValue (L.Value W n)) X) :
    (codeAt sourceCode (n + 1)).eval (pairEnvironment environment increment) =
      ((codeAt sourceCode n).eval environment, (codeAt sourceCode n).effect environment increment) :=
  eval_liftExpr (codeAt sourceCode n) environment increment

theorem next_code_total (environment increment : Env (PairValue (L.Value W n)) X) :
    ((codeAt sourceCode (n + 1)).eval (pairEnvironment environment increment)).1 +
      ((codeAt sourceCode (n + 1)).eval (pairEnvironment environment increment)).2 =
        (codeAt sourceCode n).eval (environment + increment) := by
  rw [next_code_value]
  exact (Expr.eval_update (codeAt sourceCode n) environment increment).symm

theorem next_code_total_environment (environment : Env (PairValue (PairValue (L.Value W n))) X) :
    ((codeAt sourceCode (n + 1)).eval environment).1 + ((codeAt sourceCode (n + 1)).eval environment).2 =
      (codeAt sourceCode n).eval (fun target name => (environment target name).1 + (environment target name).2) := by
  exact next_code_total sourceCode n (fun target name => (environment target name).1)
    (fun target name => (environment target name).2)

def collapseValue : (grade : Nat) → {target : Sorts} → PairValue (L.Value W grade) target → PairValue W target
  | 0, _, value => value
  | grade + 1, _, value => collapseValue grade (value.1 + value.2)

theorem code_base_value (grade : Nat) (environment : Env (PairValue (L.Value W grade)) X) :
    collapseValue grade ((codeAt sourceCode grade).eval environment) =
      sourceCode.eval (fun target name => collapseValue grade (environment target name)) := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change collapseValue grade (((codeAt sourceCode (grade + 1)).eval environment).1 +
      ((codeAt sourceCode (grade + 1)).eval environment).2) = _
    exact (congrArg (collapseValue grade) (next_code_total_environment sourceCode grade environment)).trans
      (previous (fun target name => (environment target name).1 + (environment target name).2))

theorem actual_base_value :
    collapseValue n (R.actionResultAt frame (configuration factory sourceCode n seed) (S.actualOccurrence frame)).2.2.1 =
      sourceCode.eval (fun target name => collapseValue n
        (((factory.datum n seed (A.epoch frame)).reader (S.actualOccurrence frame)).environment target name)) :=
  (congrArg (collapseValue n) (actual_value factory sourceCode n seed frame (S.actualOccurrence frame))).trans
    (code_base_value sourceCode n _)

theorem actual_updated_base_value
    (write : PairValue (L.Value W n) s → Env (PairValue (L.Value W n)) X) :
    collapseValue n (WB.oldPaid frame (configuration factory sourceCode n seed) +
      WB.nativeValue frame (configuration factory sourceCode n seed) write) =
        sourceCode.eval (fun target name => collapseValue n
          ((N.input (R.actualMaterial frame (configuration factory sourceCode n seed))).environment target name)) :=
  (congrArg (collapseValue n) (actual_updated_total factory sourceCode n seed frame write)).trans
    (code_base_value sourceCode n _)

theorem default_source_environment {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    let environment := (R.actionReader frame (configuration
      (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.defaultFactory W X s)
      sourceCode n seed) supplied).environment
    (fun target name => (environment target name).1 + (environment target name).2) =
      (SourceOperationInquiry.Context.Native.Orbit.Installation.cursorAt (A.epoch frame) supplied).next.next.next.raw.environment := by
  funext target name
  exact add_sub_cancel _ _

variable (data : SF.Packet (W := W) (X := X) (s := s) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X)
variable (currentFrame : A.M.Frame (Value := PairValue (L.Value W n)) (Var := sourceCfg.LowVar) (sort := s))

theorem next_action_code {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := current)) :
    (R.actionReader currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) supplied).expression =
      (language.symm ▸ codeAt sourceCode (n + 1) : Expr (PairValue (PairValue (L.Value W n))) sourceCfg.LowVar s) := by
  rw [AS.next_action_reader]
  exact transported_action_code language factory sourceCode (n + 1)
    (AS.nextSeed (withCalculation factory sourceCode) n data sourceCfg language) currentFrame supplied

theorem next_actual_value {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := current)) :
    (R.actionResultAt currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) supplied).2.2.1 =
      (language.symm ▸ codeAt sourceCode (n + 1) : Expr (PairValue (PairValue (L.Value W n))) sourceCfg.LowVar s).eval
        (R.actionReader currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) supplied).environment := by
  have actual := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language)).toAuthoritativeRoot
    (R.actionReader currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language)) supplied
  exact actual.trans (congrArg (fun expression => expression.eval
    (R.actionReader currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) supplied).environment)
      (next_action_code factory sourceCode n data sourceCfg language currentFrame supplied))

theorem next_actual_updated_total
    (write : PairValue (PairValue (L.Value W n)) s → Env (PairValue (PairValue (L.Value W n))) sourceCfg.LowVar) :
    WB.oldPaid currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) +
      WB.nativeValue currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) write =
        (language.symm ▸ codeAt sourceCode (n + 1) : Expr (PairValue (PairValue (L.Value W n))) sourceCfg.LowVar s).eval
          (N.input (R.actualMaterial currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language))).environment := by
  have actual := WB.updated_total currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language) write
  have expressionEq : (R.actualMaterial currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language)).raw =
      (language.symm ▸ codeAt sourceCode (n + 1) : Expr (PairValue (PairValue (L.Value W n))) sourceCfg.LowVar s) :=
    next_action_code factory sourceCode n data sourceCfg language currentFrame (S.actualOccurrence currentFrame)
  exact actual.trans (congrArg (fun expression => expression.eval
    (N.input (R.actualMaterial currentFrame (AS.nextCfg (withCalculation factory sourceCode) n data sourceCfg language))).environment) expressionEq)

def HasSourceCode (grade : Nat)
    (programme : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := s))
    (sameVar : programme.LowVar = X) : Prop :=
  ∀ (currentFrame : A.M.Frame (Value := L.Value W grade) (Var := X) (sort := s))
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := current)),
    (R.actionReader currentFrame (AS.stockCfg programme) supplied).expression =
      (sameVar.symm ▸ codeAt sourceCode grade : Expr (PairValue (L.Value W grade)) programme.LowVar s)

theorem native_after_admission_code
    (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
    HasSourceCode sourceCode (AS.nativeAfterAdmission (withCalculation factory sourceCode) packet).1
      (AS.nativeAfterAdmission (withCalculation factory sourceCode) packet).2.2.1
      (AS.nativeAfterAdmission (withCalculation factory sourceCode) packet).2.2.2.down := by
  rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    intro currentFrame current supplied
    exact next_action_code factory sourceCode grade data
      ⟨X, datum, inventory, pairInventory⟩ rfl currentFrame supplied

theorem born_after_native_code
    (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
    (generated : HasSourceCode sourceCode packet.1 packet.2.2.1 packet.2.2.2.down) :
    HasSourceCode sourceCode (AS.bornAfterNative packet).1 (AS.bornAfterNative packet).2.2.1
      (AS.bornAfterNative packet).2.2.2.down := by
  intro currentFrame current supplied
  exact (congrArg (fun raw => raw.expression)
    (AS.stock_action_reader currentFrame (AS.stockCfg packet.2.2.1) supplied)).trans
      (generated currentFrame supplied)

variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (firstLanguage : firstCfg.LowVar = X)

theorem cofinal_source_code (ordinal : Nat) :
    let packet := D.packetAt (withCalculation factory sourceCode) initial firstCfg firstLanguage (ordinal + 1)
    HasSourceCode sourceCode packet.1 packet.2.2.1 packet.2.2.2.down := by
  dsimp only
  rw [D.packetAt_successor]
  exact born_after_native_code sourceCode _ (native_after_admission_code factory sourceCode _)

theorem cofinal_actual_value (ordinal : Nat) :
    let packet := D.packetAt (withCalculation factory sourceCode) initial firstCfg firstLanguage (ordinal + 1)
    let raw := R.actionReader packet.2.1.1 (AS.stockCfg packet.2.2.1) (S.actualOccurrence packet.2.1.1)
    let environment := Eq.mp (congrArg (fun variableFamily => Env (PairValue (L.Value W packet.1)) variableFamily)
      packet.2.2.2.down) raw.environment
    collapseValue packet.1 (R.actionResultAt packet.2.1.1 (AS.stockCfg packet.2.2.1)
      (S.actualOccurrence packet.2.1.1)).2.2.1 =
        sourceCode.eval (fun target name => collapseValue packet.1 (environment target name)) := by
  have generated := cofinal_source_code factory sourceCode initial firstCfg firstLanguage ordinal
  generalize packetEq : D.packetAt (withCalculation factory sourceCode) initial firstCfg firstLanguage (ordinal + 1) = packet at generated ⊢
  rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := s) :=
      AS.stockCfg ⟨X, datum, inventory, pairInventory⟩
    let actual := S.actualOccurrence data.1
    let raw := R.actionReader data.1 cfg actual
    have paid : (R.actionResultAt data.1 cfg actual).2.2.1 = raw.expression.eval raw.environment :=
      RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
        (S.baseRoot data.1 cfg).toAuthoritativeRoot (R.actionReader data.1 cfg) actual
    have expressionEq : raw.expression = codeAt sourceCode grade := generated data.1 actual
    exact (congrArg (collapseValue grade)
      (paid.trans (congrArg (fun expression => expression.eval raw.environment) expressionEq))).trans
        (code_base_value sourceCode grade raw.environment)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
