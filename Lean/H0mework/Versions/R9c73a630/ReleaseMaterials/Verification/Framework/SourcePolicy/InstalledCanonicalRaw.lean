import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "InstalledGate"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace InstalledGate.RegisteredControls
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

example : (B.born (stopped frame) (base (1,0))).registered.input.expression.eval
 (B.born (stopped frame) (base (1,0))).activeEnvironment = ((1 : ℤ), (0 : ℤ)) := registered_value frame (1,0)
example : (B.born (stopped frame) (base (0,0))).registered.input.expression.eval
 (B.born (stopped frame) (base (0,0))).activeEnvironment = 0 := registered_value frame (0,0)
example : (B.born (stopped frame) (base (1,0))).registered.input.expression.eval
 (B.born (stopped frame) (base (1,0))).activeEnvironment ≠ 0 := by
 rw [registered_value]
 decide

example : type_of% (ActualRegisteredBornEffect.registered_effect (stopped frame) (base (1,0))) :=
 ActualRegisteredBornEffect.registered_effect (stopped frame) (base (1,0))
example : type_of% (ActualRegisteredBornEffect.registered_inverse (stopped frame) (base (0,0))) :=
 ActualRegisteredBornEffect.registered_inverse (stopped frame) (base (0,0))
example : ActualRegisteredBornEffect.F.paidCoordinate
 (ActualRegisteredBornEffect.transported (stopped frame) (base (1,0))) ≠ 0 := by
 intro same
 have zero := (ActualRegisteredBornEffect.registered_zero_iff (stopped frame) (base (1,0))).mp same
 exact (by decide : ((1 : ℤ), (0 : ℤ)) ≠ 0) ((registered_value frame (1,0)).symm.trans zero)
example : ActualRegisteredBornEffect.F.paidCoordinate
 (ActualRegisteredBornEffect.transported (stopped frame) (base (0,0))) = 0 :=
 (ActualRegisteredBornEffect.registered_zero_iff (stopped frame) (base (0,0))).mpr (registered_value frame (0,0))
#print axioms registered_value
#print axioms actual_after
#print axioms stopped_raw
end InstalledGate.RegisteredControls
universe u v
namespace InstalledGate.Direct
open RootInquiryCompletion SourceOperationEffects
namespace I
export ActualInstalledNativeRaw (stockRawRestriction stock_raw_read raw_registered rawAtNext rawAtNext_read installed_request cofinalRaw installed_effect installed_inverse installed_zero_iff installed_affine)
end I
variable {S : Type u} {W X : S → Type u} [∀ target, AddCommGroup (W target)] {s : S}
local instance gateGroups (grade : Nat) (target : S) : AddCommGroup (ActualInstalledNativeRaw.L.Value W grade target) :=
 ActualInstalledNativeRaw.L.groups W grade target
variable (frame : ActualInstalledNativeRaw.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : ActualInstalledNativeRaw.A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
example : type_of% (I.stockRawRestriction frame cfg) := I.stockRawRestriction frame cfg
example : type_of% (I.stock_raw_read frame cfg) := I.stock_raw_read frame cfg
example : type_of% (I.raw_registered frame) := I.raw_registered frame
variable (factory : ActualInstalledNativeRaw.SF.Factory W X s) (language : cfg.LowVar = X)
example (start : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language start) :
 type_of% (I.rawAtNext factory frame cfg language start branch) := I.rawAtNext factory frame cfg language start branch
example (start : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language start) :
 type_of% (I.rawAtNext_read factory frame cfg language start branch) := I.rawAtNext_read factory frame cfg language start branch
example (start : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language start) :
 type_of% (I.installed_request factory frame cfg language start branch) := I.installed_request factory frame cfg language start branch
example (ordinal : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
 (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) :
 type_of% (I.cofinalRaw factory frame cfg language ordinal branch) := I.cofinalRaw factory frame cfg language ordinal branch
example (ordinal : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
 (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) :
 type_of% (I.installed_effect factory frame cfg language ordinal branch) := I.installed_effect factory frame cfg language ordinal branch
example (ordinal : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
 (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) :
 type_of% (I.installed_inverse factory frame cfg language ordinal branch) := I.installed_inverse factory frame cfg language ordinal branch
example (ordinal : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
 (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) :
 type_of% (I.installed_zero_iff factory frame cfg language ordinal branch) := I.installed_zero_iff factory frame cfg language ordinal branch
example (ordinal : Nat) (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
 (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) :
 type_of% (I.installed_affine factory frame cfg language ordinal branch) := I.installed_affine factory frame cfg language ordinal branch
example {Result : Sort v} (ordinal : Nat)
 (admission : ActualInstalledNativeRaw.D.distance factory frame cfg language
  (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1) = 0 → Result)
 (consume : (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
  (ActualInstalledNativeRaw.D.index factory frame cfg language ordinal+1)) →
  (restriction : SourceOperationInquiry.Context.RawRestrictionAt
   (PhysicalValue := ActualInstalledNativeRaw.L.Value W branch.1.1) (PhysicalVar := X) (sort := s)
   (ActualInstalledNativeRaw.AS.presentationAt factory frame cfg language
    (ActualInstalledNativeRaw.D.index factory frame cfg language (ordinal+1))).erase) →
  type_of% (I.installed_effect factory frame cfg language ordinal branch) →
  type_of% (I.installed_inverse factory frame cfg language ordinal branch) →
  type_of% (I.installed_affine factory frame cfg language ordinal branch) →
  type_of% (I.installed_zero_iff factory frame cfg language ordinal branch) → Result) : Result :=
 ActualSourceSegmentBornEffect.consumeCofinalSegment factory frame cfg language ordinal admission
  (fun branch _payload => consume branch (I.cofinalRaw factory frame cfg language ordinal branch)
   (I.installed_effect factory frame cfg language ordinal branch)
   (I.installed_inverse factory frame cfg language ordinal branch)
   (I.installed_affine factory frame cfg language ordinal branch)
   (I.installed_zero_iff factory frame cfg language ordinal branch))
#print axioms I.stockRawRestriction
#print axioms I.stock_raw_read
#print axioms I.raw_registered
#print axioms I.rawAtNext
#print axioms I.rawAtNext_read
#print axioms I.installed_request
#print axioms I.cofinalRaw
#print axioms I.installed_effect
#print axioms I.installed_inverse
#print axioms I.installed_zero_iff
#print axioms I.installed_affine
end InstalledGate.Direct
namespace InstalledGate.RegisteredControls
open RootInquiryCompletion SourceOperationEffects
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := ()))
theorem installed_value (value : ℤ × ℤ) :
 (ActualInstalledNativeRaw.O.readRaw _ (ActualInstalledNativeRaw.stockRawRestriction
  (B.born (stopped frame) (base value)) (ActualInstalledNativeRaw.AS.stockCfg (base value)))).expression.eval
 (B.born (stopped frame) (base value)).activeEnvironment = value :=
 (congrArg (fun input => input.expression.eval (B.born (stopped frame) (base value)).activeEnvironment)
  ((ActualInstalledNativeRaw.stock_raw_read (B.born (stopped frame) (base value))
   (ActualInstalledNativeRaw.AS.stockCfg (base value))).trans
   (ActualInstalledNativeRaw.raw_registered (B.born (stopped frame) (base value))))).trans
  (registered_value frame value)
example : type_of% (installed_value frame (1,0)) := installed_value frame (1,0)
example : type_of% (installed_value frame (0,0)) := installed_value frame (0,0)
#print axioms installed_value
end InstalledGate.RegisteredControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
