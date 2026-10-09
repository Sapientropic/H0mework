import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Tower.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CP117Gate"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP117Gate.RegisteredControls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid old_paid_value old_paid_const material programme initial selected receipt nativeValue native_value)
end WB
namespace B
export ActualNativeBornSourceEffect (born actual_born_registered_expression)
end B
namespace T
export ActualNativeRelationTransport (paid paid_raw)
end T
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input expression_eval old_value)
end N
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
abbrev V := fun _ : Unit => ℤ
abbrev X := fun _ : Unit => Unit
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := ()))
def seedCfg : A.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := ()) where
 LowVar := X
 datum _ := { component := none, reader := fun {_current} _supplied => ⟨0, .var ()⟩ }
def write (value : ℤ × ℤ) : Env (PairValue V) X := fun _ _ => value
abbrev stopped := WB.selected frame seedCfg write

def base (value : ℤ × ℤ) : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := ()) where
 LowVar := X
 datum _ := {
  component := none
  reader := fun {_current} _supplied => ⟨0, .const (0,0)⟩
  nextEnvironmentReadAt := some (fun {_current} _supplied _receipt => write value) }
theorem actual_after (value : ℤ × ℤ) : (B.born (stopped frame) (base value)).activeEnvironment = write value := rfl

theorem stopped_raw : (T.paid (stopped frame)).raw = N.expression (WB.material frame seedCfg) := by
 have stable := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_read
  (WB.programme frame seedCfg write) (WB.initial frame seedCfg)
  (fun count => (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames
   (WB.initial frame seedCfg) (WB.programme frame seedCfg write) count).registered.input.expression)
  (by
   intro count paid actual
   change (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next _ _).registered.input.expression = _
   unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
   rw [actual]
   rfl) 0
 exact (T.paid_raw (stopped frame)).trans (stable.trans rfl)

theorem old_paid_zero : WB.oldPaid frame seedCfg = 0 := (WB.old_paid_value frame seedCfg).trans rfl

theorem native_zero : WB.nativeValue frame seedCfg write = 0 := by
 have same : (N.input (WB.material frame seedCfg)).environment = (WB.material frame seedCfg).environment := by
  change (0 : Env (PairValue V) X) + (0 - 0) = 0
  abel
 exact (WB.native_value frame seedCfg write).trans
  ((congrArg (fun environment => (N.expression (WB.material frame seedCfg)).eval environment) same).trans
   (N.old_value (WB.material frame seedCfg)))

theorem stopped_endpoint : (T.paid (stopped frame)).state.1 = .const 0 :=
 (WB.receipt frame seedCfg write).2.1.2.down.trans (congrArg Expr.const (native_zero frame))

theorem registered_value (value : ℤ × ℤ) :
 (B.born (stopped frame) (base value)).registered.input.expression.eval
 (B.born (stopped frame) (base value)).activeEnvironment = value := by
 let after := (B.born (stopped frame) (base value)).activeEnvironment
 have rawTerm : (WB.material frame seedCfg).raw = (.var () : Expr (PairValue V) X ()) := rfl
 have rawValue : (WB.material frame seedCfg).raw.eval after = value :=
  (congrArg (fun term : Expr (PairValue V) X () => term.eval after) rawTerm).trans
   (congrArg (fun environment : Env (PairValue V) X => environment () ()) (actual_after frame value))
 have oldEndpoint : (WB.material frame seedCfg).state.1 = (.const 0 : Expr (PairValue V) X ()) :=
  (WB.old_paid_const frame seedCfg).trans (congrArg Expr.const (old_paid_zero frame))
 have oldValue : (WB.material frame seedCfg).state.1.eval after = 0 :=
  congrArg (fun term : Expr (PairValue V) X () => term.eval after) oldEndpoint
 have firstValue : (N.expression (WB.material frame seedCfg)).eval after = value :=
  (N.expression_eval (WB.material frame seedCfg) after).trans
   ((congrArg₂ (· - ·) rawValue oldValue).trans (sub_zero value))
 have stoppedRawValue : (T.paid (stopped frame)).raw.eval after = value :=
  (congrArg (fun term : Expr (PairValue V) X () => term.eval after) (stopped_raw frame)).trans firstValue
 have stoppedValue : (T.paid (stopped frame)).state.1.eval after = 0 :=
  congrArg (fun term : Expr (PairValue V) X () => term.eval after) (stopped_endpoint frame)
 exact (congrArg (fun term : Expr (PairValue V) X () => term.eval after)
  (B.actual_born_registered_expression (stopped frame) (base value))).trans
   ((N.expression_eval (T.paid (stopped frame)) after).trans
    ((congrArg₂ (· - ·) stoppedRawValue stoppedValue).trans (sub_zero value)))

end CP117Gate.RegisteredControls

universe u
namespace CP117Gate.Direct
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift
namespace T
export ActualCofinalNativeTower (Words CommonWords NativeValue component sourceWord sourceWord_component
 registeredWord residualWord stageInventory actual_residual_inventory data compatible source_stage
 completion_fibre_generated completion_update_source)
export ActualCofinalNativeTower.SF (Factory)
export ActualCofinalNativeTower.A (Programme)
export ActualCofinalNativeTower.M (Frame)
end T
variable {S : Type u} {W X : S → Type u} [∀ target, AddCommGroup (W target)] {s : S}
local instance groups (grade : Nat) (target : S) : AddCommGroup
 (ActualCofinalNativeTower.L.Value W grade target) := ActualCofinalNativeTower.L.groups W grade target
variable (factory : T.Factory W X s) (frame : T.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : T.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

example : (T.data factory frame cfg language).Compatible := T.compatible factory frame cfg language
example (ordinal : Nat) : type_of% (T.actual_residual_inventory factory frame cfg language ordinal) :=
 T.actual_residual_inventory factory frame cfg language ordinal
example (bound : Nat) (word : T.CommonWords factory frame cfg language) (index : Fin (bound+1)) :
 type_of% (T.source_stage factory frame cfg language bound word index) :=
 T.source_stage factory frame cfg language bound word index
example (left right : T.CommonWords factory frame cfg language) :
 type_of% (T.completion_fibre_generated factory frame cfg language left right) :=
 T.completion_fibre_generated factory frame cfg language left right
example : type_of% (T.completion_update_source factory frame cfg language) :=
 T.completion_update_source factory frame cfg language

example (ordinal : Nat) : T.registeredWord factory frame cfg language ordinal ≠
 T.residualWord factory frame cfg language ordinal := by
 intro same
 have components := congrArg (T.component factory frame cfg language ordinal) same
 rw [T.registeredWord,T.residualWord,T.sourceWord_component,T.sourceWord_component] at components
 have expressions := Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) components
 have installed := (ActualCofinalInstalledRaw.installed_request factory frame cfg language ordinal).2
 change (ActualCofinalInstalledRaw.O.readRaw _
  (ActualCofinalInstalledRaw.rawAtStop factory frame cfg language ordinal)).expression =
  (ActualCofinalInstalledRaw.materialAtStop factory frame cfg language ordinal).raw at installed
 have sizes := congrArg remaining (installed.symm.trans expressions)
 rw [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget] at sizes
 omega

example (left right : Nat) (different : left ≠ right)
 (first : Expr (T.NativeValue factory frame cfg language left) X s)
 (second : Expr (T.NativeValue factory frame cfg language right) X s) :
 T.sourceWord factory frame cfg language left first ≠ T.sourceWord factory frame cfg language right second := by
 intro same
 have components := congrArg (T.component factory frame cfg language left) same
 rw [T.sourceWord_component] at components
 have zero : T.component factory frame cfg language left
  (T.sourceWord factory frame cfg language right second) = 0 := by
  change (DFinsupp.single (β := T.Words factory frame cfg language) right
   (Finsupp.single second (1 : ℤ))) left = 0
  exact DFinsupp.single_eq_of_ne different
 rw [zero] at components
 exact (one_ne_zero : (1 : ℤ) ≠ 0) (Finsupp.single_eq_zero.mp components)

example (ordinal : Nat) : T.sourceWord factory frame cfg language ordinal (.const 0) ≠ 0 := by
 intro same
 have projected := congrArg (T.component factory frame cfg language ordinal) same
 rw [T.sourceWord_component,map_zero] at projected
 exact (one_ne_zero : (1 : ℤ) ≠ 0) (Finsupp.single_eq_zero.mp projected)

example (ordinal : Nat) : (ActualCofinalNativeTower.sourceMap factory frame cfg language).hom
 (T.sourceWord factory frame cfg language ordinal (.const 0)) = 0 := by
 apply (ActualCofinalNativeTower.completion_zero_iff factory frame cfg language _).mpr
 intro site
 by_cases same : site = ordinal
 · subst site
   change ActualCofinalNativeTower.nativeInventory factory frame cfg language ordinal
    (T.component factory frame cfg language ordinal
     (T.sourceWord factory frame cfg language ordinal (.const 0))) = 0
   rw [T.sourceWord_component]
   simp only [ActualCofinalNativeTower.nativeInventory,updateInventory,LinearMap.prod_apply,Function.prod,
    SourceOperationScalarRelations.evaluation,effectEvaluator,Finsupp.linearCombination_single,
    one_smul,Expr.eval,Expr.effect,Prod.zero_eq_mk]
 · have zero : T.component factory frame cfg language site
    (T.sourceWord factory frame cfg language ordinal (.const 0)) = 0 := by
    change (DFinsupp.single (β := T.Words factory frame cfg language) ordinal
     (Finsupp.single (.const 0) (1 : ℤ))) site = 0
    exact DFinsupp.single_eq_of_ne same
   change ActualCofinalNativeTower.nativeInventory factory frame cfg language site
    (T.component factory frame cfg language site
     (T.sourceWord factory frame cfg language ordinal (.const 0))) = 0
   rw [zero,map_zero]

end CP117Gate.Direct

namespace CP117Gate.SourceControls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift
namespace C
export CP117Gate.RegisteredControls (V X seedCfg stopped base write old_paid_zero native_zero registered_value)
end C
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (defaultFactory)
end SF
namespace T
export ActualCofinalNativeTower (registeredWord residualWord stageInventory oldEnvironment actualIncrement updatedEnvironment updated_environment installed_environment)
end T
local instance controlGroups (grade : Nat) (target : Unit) : AddCommGroup
 (ActualCofinalNativeTower.L.Value (PairValue C.V) grade target) :=
 ActualCofinalNativeTower.L.groups (PairValue C.V) grade target
variable (frame : CP117Gate.RegisteredControls.A.M.Frame (Value := C.V) (Var := C.X) (sort := ()))
abbrev initial (value : ℤ × ℤ) := ActualNativeBornSourceEffect.born (C.stopped frame) (C.base value)
abbrev factory := SF.defaultFactory (PairValue C.V) C.X ()

theorem site_old (value : ℤ × ℤ) :
 T.oldEnvironment factory (initial frame value) (C.base value) rfl 0 = 0 := by
 rw [T.installed_environment]
 have source := (ActualCofinalInstalledRaw.materialAtStop_source
  factory (initial frame value) (C.base value) rfl 0).1
 have original : (ActualCofinalInstalledRaw.packet
  factory (initial frame value) (C.base value) rfl 0).2.1.1 = initial frame value := rfl
 rw [original] at source
 have bornEnv := ActualNativeBornSourceEffect.actual_born_registered_environment
  (C.stopped frame) (C.base value)
 apply source.trans
 apply bornEnv.trans
 have stable := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_read
  (CP117Gate.RegisteredControls.WB.programme frame C.seedCfg CP117Gate.RegisteredControls.write)
  (CP117Gate.RegisteredControls.WB.initial frame C.seedCfg)
  (fun count => SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames
    (CP117Gate.RegisteredControls.WB.initial frame C.seedCfg)
    (CP117Gate.RegisteredControls.WB.programme frame C.seedCfg CP117Gate.RegisteredControls.write) count) 0)
  (by
   intro count paid actual
   change SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next _ _) 0 = _
   unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
   rw [actual]
   rfl) 0
 have first : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
  (CP117Gate.RegisteredControls.WB.initial frame C.seedCfg) 0 := by
  intro current occurrence
  rfl
 have selected : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
  (C.stopped frame) 0 := @Eq.mpr _ _ stable @first
 exact SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active @selected


attribute [local irreducible] ActualCofinalInstalledRaw.currentAtStop

private theorem increment_transport
 (first second : AnyAuthoritativeRootCurrent.{0}) (same : first = second)
 (material : ActualCanonicalBornSource.MaterialAtCurrent (Value := PairValue C.V) (Var := C.X) (s := ()) first) :
 (Eq.mp (congrArg (ActualCanonicalBornSource.MaterialAtCurrent
  (Value := PairValue C.V) (Var := C.X) (s := ())) same) material).increment = material.increment := by
 subst second
 rfl

theorem site_updated (value : ℤ × ℤ) :
 T.updatedEnvironment factory (initial frame value) (C.base value) rfl 0 = C.write value := by
 have original : (ActualCofinalInstalledRaw.packet
  factory (initial frame value) (C.base value) rfl 0).2.1.1 = initial frame value := rfl
 have env := (ActualCofinalInstalledRaw.materialAtStop_source
  factory (initial frame value) (C.base value) rfl 0).1
 rw [original] at env
 have increment := increment_transport
  (ActualInstalledNativeRaw.SO.current (initial frame value) (C.base value))
  (ActualCofinalInstalledRaw.currentAtStop factory (initial frame value) (C.base value) rfl 0)
  (ActualCofinalInstalledRaw.actual_current factory (initial frame value) (C.base value) rfl 0).symm
  (ActualNativeRelationTransport.paid (initial frame value))
 have increment' : (ActualCofinalInstalledRaw.materialAtStop
  factory (initial frame value) (C.base value) rfl 0).increment =
  (ActualNativeRelationTransport.paid (initial frame value)).increment := increment
 have actual : (ActualNativeRelationTransport.paid (initial frame value)).increment =
  (initial frame value).activeEnvironment - (initial frame value).registered.input.environment := rfl
 rw [T.updated_environment,T.installed_environment]
 dsimp only [T.actualIncrement]
 rw [env,increment',actual,add_sub_cancel]
 exact CP117Gate.RegisteredControls.actual_after frame value

theorem site_inventory (value : ℤ × ℤ) :
 T.stageInventory factory (initial frame value) (C.base value) rfl 0
  (T.registeredWord factory (initial frame value) (C.base value) rfl 0) = (0,value) := by
 have original : (ActualCofinalInstalledRaw.packet
  factory (initial frame value) (C.base value) rfl 0).2.1.1 = initial frame value := rfl
 have read := ActualCofinalInstalledRaw.rawAtStop_read factory (initial frame value) (C.base value) rfl 0
 rw [original] at read
 have expression := congrArg (fun raw => raw.expression) read
 have same : (initial frame value).registered.input.expression = (initial frame (0,0)).registered.input.expression :=
  (ActualNativeBornSourceEffect.actual_born_registered_expression (C.stopped frame) (C.base value)).trans
   (ActualNativeBornSourceEffect.actual_born_registered_expression (C.stopped frame) (C.base (0,0))).symm
 have old : (initial frame value).registered.input.expression.eval (0 : Env (PairValue C.V) C.X) = 0 := by
  rw [same]
  exact (congrArg (fun env => (initial frame (0,0)).registered.input.expression.eval env)
   (CP117Gate.RegisteredControls.actual_after frame (0,0))).symm.trans
   (C.registered_value frame (0,0))
 have next : (initial frame value).registered.input.expression.eval (C.write value) = value :=
  (congrArg (fun env => (initial frame value).registered.input.expression.eval env)
   (CP117Gate.RegisteredControls.actual_after frame value)).symm.trans (C.registered_value frame value)
 change ActualCofinalNativeTower.nativeInventory factory (initial frame value) (C.base value) rfl 0
  (ActualCofinalNativeTower.component factory (initial frame value) (C.base value) rfl 0
   (T.registeredWord factory (initial frame value) (C.base value) rfl 0)) = _
 rw [T.registeredWord,ActualCofinalNativeTower.sourceWord_component]
 simp only [ActualCofinalNativeTower.nativeInventory,updateInventory,LinearMap.prod_apply,Function.prod,
  SourceOperationScalarRelations.evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
 rw [expression]
 change ((initial frame value).registered.input.expression.eval
  (T.oldEnvironment factory (initial frame value) (C.base value) rfl 0),
  (initial frame value).registered.input.expression.effect
   (T.oldEnvironment factory (initial frame value) (C.base value) rfl 0)
   (T.actualIncrement factory (initial frame value) (C.base value) rfl 0)) = _
 apply Prod.ext
 · rw [site_old]
   exact old
 · have generated := Expr.eval_update (initial frame value).registered.input.expression
    (T.oldEnvironment factory (initial frame value) (C.base value) rfl 0)
    (T.actualIncrement factory (initial frame value) (C.base value) rfl 0)
   rw [← T.updated_environment,site_updated,next,site_old,old,zero_add] at generated
   simpa only [site_old] using generated.symm

example : T.stageInventory factory (initial frame (1,0)) (C.base (1,0)) rfl 0
 (T.registeredWord factory (initial frame (1,0)) (C.base (1,0)) rfl 0) = (0,((1 : ℤ),0)) :=
 site_inventory frame (1,0)
example : T.stageInventory factory (initial frame (0,0)) (C.base (0,0)) rfl 0
 (T.registeredWord factory (initial frame (0,0)) (C.base (0,0)) rfl 0) = 0 :=
 site_inventory frame (0,0)

end CP117Gate.SourceControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
