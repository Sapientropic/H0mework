import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Read

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKAction

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations
open OriginalKCofinalFullBranchFibre.KernelWrite

namespace U
export BoundaryCountedNativeUpdate (selected sourceMaterial base result resultValue writtenUpdate updated_source actual_physical)
end U
namespace N
export BoundaryCountedNativeWord (NextValues nextChart gradeChart updated_source)
end N
namespace QI
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (resultFace)
end QI
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base root baseRoot actualOccurrence visit)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt actionReader afterEnvironment)
end R
namespace MR
export SourceGeneratedInquiryReceiptAction.Read
  (raw_source environment_source increment_source updated_environment_source state_source
   occurrence_source value_source paid_source after_environment_source)
end MR

namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (programme born material oldPaid nativeValue old_paid_value configured_actual_paid_pair_writeback source_whole source_target_next)
end WB

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "T" => OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceCayley
local notation "Ppos" => HilbertInventory.positionSpace.toSubmodule.starProjection
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate

local instance groups (grade : Nat) : ∀ slot, AddCommGroup (L.Value (PairValue C.Value) grade slot) :=
  L.groups (PairValue C.Value) grade

abbrev Grade (grade : Nat) := L.Value (PairValue C.Value) grade

private def leafValue (f : BurnolL2 →+ BurnolL2) : (grade : Nat) → (slot : Unit) → Grade grade slot → Grade grade slot
  | 0, (), value => (f value.1,f value.2)
  | grade+1, slot, value => (leafValue f grade slot value.1,leafValue f grade slot value.2)

private theorem leaf_zero (f : BurnolL2 →+ BurnolL2) (grade : Nat) (slot : Unit) :
    leafValue f grade slot 0 = 0 := by
  induction grade with
  | zero => cases slot; exact Prod.ext (map_zero f) (map_zero f)
  | succ grade previous => exact Prod.ext previous previous

private theorem leaf_add (f : BurnolL2 →+ BurnolL2) (grade : Nat) (slot : Unit)
    (x y : Grade grade slot) : leafValue f grade slot (x+y) = leafValue f grade slot x + leafValue f grade slot y := by
  induction grade with
  | zero => cases slot; exact Prod.ext (map_add f x.1 y.1) (map_add f x.2 y.2)
  | succ grade previous => exact Prod.ext (previous x.1 y.1) (previous x.2 y.2)

def leaves (f : BurnolL2 →+ BurnolL2) (grade : Nat) (slot : Unit) : Grade grade slot →+ Grade grade slot where
  toFun := leafValue f grade slot
  map_zero' := leaf_zero f grade slot
  map_add' := leaf_add f grade slot

def total : (grade : Nat) → Grade grade () →+ BurnolL2
  | 0 => (AddMonoidHom.fst BurnolL2 BurnolL2) + (AddMonoidHom.snd BurnolL2 BurnolL2)
  | grade+1 => by
    letI : AddCommGroup (Grade grade ()) := L.groups (PairValue C.Value) grade ()
    exact (total grade).comp (AddMonoidHom.fst _ _) + (total grade).comp (AddMonoidHom.snd _ _)

theorem total_leaves (f : BurnolL2 →+ BurnolL2) (grade : Nat) (value : Grade grade ()) :
    total grade (leaves f grade () value) = f (total grade value) := by
  induction grade with
  | zero => exact (map_add f value.1 value.2).symm
  | succ grade previous =>
    change total grade (leaves f grade () value.1) + total grade (leaves f grade () value.2) =
      f (total grade value.1 + total grade value.2)
    rw [previous, previous, map_add]

private theorem total_chart (coordinate : BurnolCompletedMellinCoordinate) (n grade : Nat)
    (value : Grade grade ()) : total grade (N.gradeChart coordinate n grade () value) =
      BoundaryCountedWordInverse.equiv coordinate n (total grade value) := by
  induction grade with
  | zero => exact (map_add (BoundaryCountedWordInverse.equiv coordinate n) value.1 value.2).symm
  | succ grade previous =>
    change total grade (N.gradeChart coordinate n grade () value.1) +
      total grade (N.gradeChart coordinate n grade () value.2) =
        BoundaryCountedWordInverse.equiv coordinate n (total grade value.1 + total grade value.2)
    exact (congrArg₂ (fun x y : BurnolL2 => x+y) (previous value.1) (previous value.2)).trans
      (map_add (BoundaryCountedWordInverse.equiv coordinate n) _ _).symm

private theorem total_chart_inverse (coordinate : BurnolCompletedMellinCoordinate) (n grade : Nat)
    (value : Grade grade ()) : total grade ((N.gradeChart coordinate n grade ()).symm value) =
      (BoundaryCountedWordInverse.equiv coordinate n).symm (total grade value) := by
  have forward := total_chart coordinate n grade ((N.gradeChart coordinate n grade ()).symm value)
  rw [(N.gradeChart coordinate n grade ()).apply_symm_apply] at forward
  exact ((congrArg (BoundaryCountedWordInverse.equiv coordinate n).symm forward).trans
    ((BoundaryCountedWordInverse.equiv coordinate n).symm_apply_apply _)).symm

private theorem total_cast {first second : Nat} (same : first=second) (value : Grade first ()) :
    total second (Eq.mp (congrArg (fun grade => Grade grade ()) same) value) = total first value := by
  cases same
  rfl

private theorem total_collapse (grade : Nat) (value : PairValue (Grade grade) ()) :
    total 1 (CF.collapseValue (W := PairValue C.Value) grade value) = total (grade+1) value := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change total 1 (CF.collapseValue grade (value.1+value.2)) = _
    rw [previous, map_add]
    rfl

private theorem total_branches (value : BoundaryCountedNativeBeta.Branches) :
    total 1 value = BoundaryCountedNativeBeta.total value := rfl

private theorem total_native (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (value : Grade (AS.nativeAfterAdmission factory packet).1 ()) :
    total 1 (NativeSigma.collapseNative factory packet value) =
      total (AS.nativeAfterAdmission factory packet).1 value := by
  unfold NativeSigma.collapseNative
  exact (total_collapse packet.1 _).trans (total_cast (AS.nativeAfterAdmission_grade factory packet) value)

namespace Program
variable (coordinate : BurnolCompletedMellinCoordinate) (n grade : Nat)
local notation "V" => Grade grade

def lift (f : End) : PairValue V () →+ PairValue V () :=
  (leaves f.toLinearMap.toAddMonoidHom grade ()).prodMap (leaves f.toLinearMap.toAddMonoidHom grade ())

def decode : PairValue V () →+ PairValue V () :=
  ((N.gradeChart coordinate n grade ()).symm.prodCongr (N.gradeChart coordinate n grade ()).symm).toAddMonoidHom

def start : Expr (PairValue V) C.Var () := .linear (decode coordinate n grade) (.var ())

def adjointSteps : Nat → Expr (PairValue V) C.Var ()
  | 0 => start coordinate n grade
  | k+1 => .linear (lift grade (T (C coordinate)).adjoint) (adjointSteps k)

def code (order : Nat) : Expr (PairValue V) C.Var () :=
  let z := adjointSteps coordinate n grade order
  .linear (lift grade P) (.add z (.linear (-AddMonoidHom.id _) 
    (.linear (lift grade (T (C coordinate))) (.linear (lift grade Ppos)
      (.linear (lift grade (T (C coordinate)).adjoint) z)))))

theorem budget (order : Nat) : remaining (code coordinate n grade order) = 2*order+10 := by
  have count (k : Nat) : remaining (adjointSteps coordinate n grade k) = k+2 := by
    induction k with
    | zero => rfl
    | succ k previous => change remaining (adjointSteps coordinate n grade k)+1 = k+1+2; omega
  simp only [code, remaining, count]
  omega
theorem decode_total (value : PairValue V ()) :
    total (grade+1) (decode coordinate n grade value) =
      total grade ((N.gradeChart coordinate n grade ()).symm (value.1+value.2)) := by
  change total grade ((N.gradeChart coordinate n grade ()).symm value.1) +
    total grade ((N.gradeChart coordinate n grade ()).symm value.2) = _
  rw [← map_add, ← map_add]

theorem lift_total (f : End) (value : PairValue V ()) :
    total (grade+1) (lift grade f value) = f (total (grade+1) value) :=
  total_leaves f.toLinearMap.toAddMonoidHom (grade+1) value

theorem steps_total (order : Nat) (environment : Env (PairValue V) C.Var) :
    total (grade+1) ((adjointSteps coordinate n grade order).eval environment) =
      ((T (C coordinate)).adjoint^order)
        (total (grade+1) (decode coordinate n grade (environment () ()))) := by
  induction order with
  | zero => rfl
  | succ order previous =>
    change total (grade+1) (lift grade (T (C coordinate)).adjoint
      ((adjointSteps coordinate n grade order).eval environment)) = _
    rw [lift_total, previous, pow_succ', mul_apply_eq_comp]

theorem code_total (order : Nat) (environment : Env (PairValue V) C.Var) :
    total (grade+1) ((code coordinate n grade order).eval environment) =
      let z := ((T (C coordinate)).adjoint^order)
        (total (grade+1) (decode coordinate n grade (environment () ())))
      P (z - T (C coordinate) (Ppos ((T (C coordinate)).adjoint z))) := by
  simp only [code, Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    lift_total, map_add, map_neg, steps_total, sub_eq_add_neg]

end Program

private theorem raw_environment {W X : Unit → Type} [∀ slot, AddCommGroup (W slot)]
    (env : Env W X) (term : Expr W X ()) :
    (⟨env,term⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := W) (Var := X) (sort := ())).environment = env := rfl

private theorem raw_environment_congr {W X : Unit → Type} [∀ slot, AddCommGroup (W slot)]
    {left right : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := W) (Var := X) (sort := ())}
    (same : left=right) : left.environment = right.environment :=
  congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := W) (Var := X) (sort := ()) => raw.environment) same


private def constant_environment {W X : Unit → Type} (value : W ()) : Env W X := fun slot _ => by
  cases slot
  exact value

private theorem constant_environment_read {W X : Unit → Type} (value : W ()) (name : X ()) :
    (constant_environment (X := X) value) () name = value := rfl

private theorem environment_read_congr {W X : Unit → Type} {before after : Env W X}
    (same : before=after) (name : X ()) : before () name = after () name :=
  congrArg (fun env : Env W X => env () name) same

private theorem after_environment_of_reader {W X : Unit → Type} [∀ slot, AddCommGroup (W slot)]
    (frame : A.M.Frame (Value := W) (Var := X) (sort := ()))
    (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := ()))
    (env : Env (PairValue W) cfg.LowVar)
    (fixed : (receiver : A.M.Frame (Value := W) (Var := X) (sort := ())) →
      {current : J.Current receiver.registered} → (supplied : I.Occurrence receiver (current := current)) →
      (R.actionReader receiver cfg supplied).environment = env) :
    R.afterEnvironment frame cfg = env :=
  (MR.after_environment_source frame cfg).trans
    (fixed (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg)
      (S.actualOccurrence (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg)))

section Native
variable (coordinate : BurnolCompletedMellinCoordinate) (n order : Nat)
variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
local notation "V" => N.NextValues factory native
local notation "f" => U.selected factory native
local notation "cfg" => BoundaryCountedNativeQuery.configuration factory native

abbrev originalResult := U.result coordinate n factory native

def receiptValue (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (origin : (QI.resultFace (U.base factory native)
      (BoundaryCountedNativeUpdate.reader coordinate n factory native)).Restriction) :
    PairValue (N.NextValues factory native) () := origin.2.2.1

def sourceValue : PairValue V () :=
  receiptValue coordinate n factory native (originalResult coordinate n factory native)

def environment : Env (PairValue V) C.Var :=
  constant_environment (sourceValue coordinate n factory native)

variable (receiver : A.M.Frame (Value := V) (Var := C.Var) (sort := ()))
variable {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current))

structure SourceAt (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) where
  original : (QI.resultFace (U.base factory native)
    (BoundaryCountedNativeUpdate.reader coordinate n factory native)).Restriction
  currentMaterial : type_of% (I.materialAt receiver supplied)


def originAt (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    SourceAt coordinate n factory native receiver supplied := {
  original := originalResult coordinate n factory native
  currentMaterial := I.materialAt receiver supplied }

def sourceLaw (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ())) :
    SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => SourceAt coordinate n factory native receiver occurrence
  project := fun _ {_current} occurrence _ => originAt coordinate n factory native receiver occurrence

def sourceRaw (coordinate : BurnolCompletedMellinCoordinate) (n order : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (_supplied : I.Occurrence receiver (current := current)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue (N.NextValues factory native)) (Var := C.Var) (sort := ()) :=
  ⟨environment coordinate n factory native,
    Program.code coordinate n (NativeDelta.BetaDecoder.nextNative factory native).1 order⟩

theorem source_environment (coordinate : BurnolCompletedMellinCoordinate) (n order : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    (sourceRaw coordinate n order factory native receiver supplied).environment =
      environment coordinate n factory native :=
  @raw_environment (PairValue (N.NextValues factory native)) C.Var
    (fun slot => @Prod.instAddCommGroup (N.NextValues factory native slot) (N.NextValues factory native slot)
      (groups (NativeDelta.BetaDecoder.nextNative factory native).1 slot)
      (groups (NativeDelta.BetaDecoder.nextNative factory native).1 slot))
    (environment coordinate n factory native)
    (Program.code coordinate n (NativeDelta.BetaDecoder.nextNative factory native).1 order)

def fullSource (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
    (receiver : A.M.Frame (Value := N.NextValues factory native) (Var := C.Var) (sort := ())) :=
  (S.root receiver (BoundaryCountedNativeQuery.configuration factory native)).source.base.withProjectionCoface
    (sourceLaw coordinate n factory native receiver)

def configuration (coordinate : BurnolCompletedMellinCoordinate) (n order : Nat)
    (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :
    A.Programme (PhysicalValue := N.NextValues factory native) (PhysicalVar := C.Var) (sort := ()) :=
  let original := BoundaryCountedNativeQuery.configuration factory native
  let language : original.LowVar = C.Var := (NativeDelta.BetaDecoder.nextNative factory native).2.2.2.down
  { LowVar := C.Var
    datum := fun receiver =>
      let prior : SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum C.Var receiver :=
        Eq.mp (congrArg (fun vars => SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum vars receiver)
          language) (original.datum receiver)
      { prior with
        component := some (fullSource coordinate n factory native receiver).projectionLaw
        reader := sourceRaw coordinate n order factory native receiver
        calculationReader := none }
    nextInventory := original.nextInventory
    nextPairInventory := original.nextPairInventory }

abbrev material := R.actualMaterial f (configuration coordinate n order factory native)
abbrev actualResult := R.actionResultAt f (configuration coordinate n order factory native)
  (SourceGeneratedInquiryReceiptAction.occurrence f (configuration coordinate n order factory native))

theorem original_ledger :
    (S.baseRoot f (configuration coordinate n order factory native)).toAuthoritativeRoot.toLedgerRoot =
      (U.base factory native).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_occurrence : HEq
    (SourceGeneratedInquiryReceiptAction.occurrence f (configuration coordinate n order factory native))
    ((U.base factory native).root.emitted (U.base factory native).visit.current) :=
  (heq_of_eq (MR.occurrence_source f (configuration coordinate n order factory native))).trans HEq.rfl

/-- Retain the complete result generated at the original paid occurrence. -/
theorem source_reader (receiver : A.M.Frame (Value := V) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    R.actionReader receiver (configuration coordinate n order factory native) supplied =
      sourceRaw coordinate n order factory native (A.epoch receiver) supplied := rfl

theorem material_raw :
    (material coordinate n order factory native).raw =
      Program.code coordinate n (NativeDelta.BetaDecoder.nextNative factory native).1 order :=
  (MR.raw_source f (configuration coordinate n order factory native)).trans
    (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue V) (Var := C.Var) (sort := ()) => raw.expression)
      (source_reader coordinate n order factory native f
        (SourceGeneratedInquiryReceiptAction.occurrence f (configuration coordinate n order factory native))))

theorem material_environment :
    (material coordinate n order factory native).environment = environment coordinate n factory native :=
  (MR.environment_source f (configuration coordinate n order factory native)).trans
    ((raw_environment_congr (source_reader coordinate n order factory native f
      (SourceGeneratedInquiryReceiptAction.occurrence f (configuration coordinate n order factory native)))).trans
      (source_environment coordinate n order factory native (A.epoch f)
        (SourceGeneratedInquiryReceiptAction.occurrence f (configuration coordinate n order factory native))))

attribute [local irreducible] SourceGeneratedInquiryReceiptAction.material
  SourceGeneratedInquiryReceiptAction.actionResultAt

theorem original_input :
    (material coordinate n order factory native).environment () () = sourceValue coordinate n factory native :=
  (environment_read_congr (material_environment coordinate n order factory native) ()).trans
    (constant_environment_read (X := C.Var) (sourceValue coordinate n factory native) ())

theorem original_receipt :
    ((sourceLaw coordinate n factory native (A.epoch f)).project PUnit.unit (S.actualOccurrence f) PUnit.unit).original =
      originalResult coordinate n factory native := rfl

theorem origin_value :
    receiptValue coordinate n factory native
      (((sourceLaw coordinate n factory native (A.epoch f)).project PUnit.unit (S.actualOccurrence f) PUnit.unit).original) =
        sourceValue coordinate n factory native :=
  congrArg (receiptValue coordinate n factory native) (original_receipt coordinate n factory native)

theorem input_from_original_receipt :
    (material coordinate n order factory native).environment () () =
      receiptValue coordinate n factory native
        (((sourceLaw coordinate n factory native (A.epoch f)).project PUnit.unit (S.actualOccurrence f) PUnit.unit).original) :=
  (original_input coordinate n order factory native).trans (origin_value coordinate n factory native).symm

theorem actual_equation :
    (actualResult coordinate n order factory native).2.2.1 =
      (Program.code coordinate n (NativeDelta.BetaDecoder.nextNative factory native).1 order).eval
        (environment coordinate n factory native) :=
  (MR.value_source f (configuration coordinate n order factory native)).trans
    (congrArg₂ (fun term env => Expr.eval term env)
      (material_raw coordinate n order factory native) (material_environment coordinate n order factory native))

theorem actual_paid :
    (material coordinate n order factory native).state.2.length = 2*order+10 :=
  (MR.paid_source f (configuration coordinate n order factory native)).trans
    ((congrArg remaining (material_raw coordinate n order factory native)).trans
      (Program.budget coordinate n _ order))

/-- The fixed original source result is retained at this action's actual next receiver. -/
theorem after_environment :
    R.afterEnvironment f (configuration coordinate n order factory native) = environment coordinate n factory native := by
  apply after_environment_of_reader f (configuration coordinate n order factory native)
    (environment coordinate n factory native)
  intro receiver current supplied
  exact (raw_environment_congr (source_reader coordinate n order factory native receiver supplied)).trans
    (source_environment coordinate n order factory native (A.epoch receiver) supplied)

theorem input_environment :
    (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
      (material coordinate n order factory native)).environment =
        (material coordinate n order factory native).environment :=
  (MR.updated_environment_source f (configuration coordinate n order factory native)).trans
    ((after_environment coordinate n order factory native).trans
      (material_environment coordinate n order factory native).symm)

def write (value : PairValue V ()) : Env (PairValue V) C.Var := fun target _ => by cases target; exact value

abbrev born := WB.born f (configuration coordinate n order factory native) (write factory native)
abbrev target := SourceGeneratedInquiryReceiptAction.Configured.Writeback.sourceTarget f
  (configuration coordinate n order factory native) (write factory native)

theorem actual_born_write :
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
      (born coordinate n order factory native)
      (write factory native ((material coordinate n order factory native).raw.eval
        (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
          (material coordinate n order factory native)).environment)) :=
  WB.configured_actual_paid_pair_writeback f (configuration coordinate n order factory native) (write factory native)

theorem born_value :
    (born coordinate n order factory native).activeEnvironment () () =
      (actualResult coordinate n order factory native).2.2.1 := by
  have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
    (actual_born_write coordinate n order factory native)
  have value := congrArg (fun env : Env (PairValue V) C.Var => env () ()) written
  have paid : (material coordinate n order factory native).raw.eval
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
        (material coordinate n order factory native)).environment =
        (actualResult coordinate n order factory native).2.2.1 :=
    (congrArg (Expr.eval (material coordinate n order factory native).raw)
      (input_environment coordinate n order factory native)).trans
      (MR.value_source f (configuration coordinate n order factory native)).symm
  exact value.trans paid

def decodedTotal : BurnolL2 :=
  total ((NativeDelta.BetaDecoder.nextNative factory native).1+1)
    (Program.decode coordinate n (NativeDelta.BetaDecoder.nextNative factory native).1
      (sourceValue coordinate n factory native))

theorem decoded_source :
    decodedTotal coordinate n factory native =
      (BoundaryCountedWordInverse.equiv coordinate n).symm
        (BoundaryCountedNativeBeta.total (NativeSigma.collapseNative factory (AS.bornAfterNative native)
          (U.writtenUpdate coordinate n factory native))) := by
  have decoded : decodedTotal coordinate n factory native =
      total (NativeDelta.BetaDecoder.nextNative factory native).1
        ((N.nextChart coordinate n factory native ()).symm (U.writtenUpdate coordinate n factory native)) :=
    Program.decode_total coordinate n _ (sourceValue coordinate n factory native)
  exact decoded.trans ((total_chart_inverse coordinate n _ (U.writtenUpdate coordinate n factory native)).trans
    (congrArg (BoundaryCountedWordInverse.equiv coordinate n).symm
      ((total_native factory (AS.bornAfterNative native) (U.writtenUpdate coordinate n factory native)).symm.trans
        (total_branches _))))

theorem born_field :
    total ((NativeDelta.BetaDecoder.nextNative factory native).1+1)
      ((born coordinate n order factory native).activeEnvironment () ()) =
      BoundaryNativeKRead.field coordinate order (decodedTotal coordinate n factory native) := by
  have paid := congrArg (total ((NativeDelta.BetaDecoder.nextNative factory native).1+1))
    (born_value coordinate n order factory native)
  have computed := congrArg (total ((NativeDelta.BetaDecoder.nextNative factory native).1+1))
    (actual_equation coordinate n order factory native)
  exact paid.trans (computed.trans ((Program.code_total coordinate n _ order
    (environment coordinate n factory native)).trans
      (BoundaryNativeKRead.field_apply coordinate order (decodedTotal coordinate n factory native)).symm))

theorem source_trace_in_next_stock :
    SourceGeneratedInquiryReceiptAction.Configured.lowStock f (configuration coordinate n order factory native) =
      SourceOperationPaidRelations.exposure (material coordinate n order factory native).state.2 ∧
    type_of% (MR.state_source f (configuration coordinate n order factory native)) :=
  ⟨rfl, MR.state_source f (configuration coordinate n order factory native)⟩

theorem source_stock_written :
    (SourceGeneratedInquiryReceiptAction.Configured.lowInitial f
      (configuration coordinate n order factory native)).inventory =
      some (SourceGeneratedInquiryReceiptAction.Configured.lowWritten f
        (configuration coordinate n order factory native)) := rfl

theorem born_inventory : type_of% (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born_inventory
    f (configuration coordinate n order factory native) (write factory native)) :=
  SourceGeneratedInquiryReceiptAction.Configured.Writeback.born_inventory
    f (configuration coordinate n order factory native) (write factory native)

theorem actual_receipt_next : type_of% (SourceGeneratedInquiryReceiptAction.Configured.Writeback.actual_receipt_next
    f (configuration coordinate n order factory native) (write factory native)) :=
  SourceGeneratedInquiryReceiptAction.Configured.Writeback.actual_receipt_next
    f (configuration coordinate n order factory native) (write factory native)

theorem whole_first : type_of% (WB.source_whole f (configuration coordinate n order factory native) (write factory native)) :=
  WB.source_whole f (configuration coordinate n order factory native) (write factory native)

theorem generated_next : type_of% (WB.source_target_next f (configuration coordinate n order factory native)
    (write factory native)) :=
  WB.source_target_next f (configuration coordinate n order factory native) (write factory native)
end Native

attribute [local irreducible] AS.localNativeReceipt

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth
local notation "amount" => BoundaryNativeKRead.amplitude observation nontrivial half depth
local notation "readInput" => BoundaryNativeKRead.input observation nontrivial half depth

private theorem original_decoded (ordinal n : Nat) :
    decodedTotal c n factory (nativeAt (ordinal+1)) = readInput ordinal n :=
  decoded_source c n factory (nativeAt (ordinal+1))

def physical (ordinal n : Nat) : BurnolL2 :=
  total ((NativeDelta.BetaDecoder.nextNative factory (nativeAt (ordinal+1))).1+1)
    ((born c n m factory (nativeAt (ordinal+1))).activeEnvironment () ())

private theorem physical_field (ordinal n : Nat) : physical observation nontrivial half depth ordinal n =
    BoundaryNativeKRead.field c m (readInput ordinal n) :=
  (born_field c n m factory (nativeAt (ordinal+1))).trans
    (congrArg (BoundaryNativeKRead.field c m) (original_decoded observation nontrivial half depth ordinal n))

/-- The new actual terminal is written into the next original inventory before K is recognized. -/
theorem actual_born_K (ordinal n : Nat) : physical observation nontrivial half depth ordinal n =
    amount ordinal • (burnolCompletedMellinRieszVector c : BurnolL2) :=
  (physical_field observation nontrivial half depth ordinal n).trans
    (BoundaryNativeKRead.field_source observation nontrivial half depth ordinal n)

theorem actual_born_fixed_price (ordinal n : Nat) :
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)
      (physical observation nontrivial half depth ordinal n) = amount ordinal *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) :=
  (congrArg (fun value : BurnolL2 => inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) value)
    (physical_field observation nontrivial half depth ordinal n)).trans
      (BoundaryNativeKRead.fixed_price observation nontrivial half depth ordinal n)

theorem actual_born_live (ordinal n : Nat) : physical observation nontrivial half depth ordinal n ≠ 0 := by
  rw [physical_field]
  exact BoundaryNativeKRead.field_live observation nontrivial half depth ordinal n

/-- The independent fixed B consumes this same born field together with the new receipt's whole and next. -/
theorem actual_K_writeback (ordinal n : Nat) :
    physical observation nontrivial half depth ordinal n = amount ordinal • (burnolCompletedMellinRieszVector c : BurnolL2) ∧
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)
      (physical observation nontrivial half depth ordinal n) = amount ordinal *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) ∧
    physical observation nontrivial half depth ordinal n ≠ 0 ∧
    type_of% (actual_paid c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (original_ledger c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (original_occurrence c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (input_from_original_receipt c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (MR.increment_source (U.selected factory (nativeAt (ordinal+1)))
      (configuration c n m factory (nativeAt (ordinal+1)))) ∧
    type_of% (source_trace_in_next_stock c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (source_stock_written c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (born_inventory c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (actual_receipt_next c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (whole_first c n m factory (nativeAt (ordinal+1))) ∧
    type_of% (generated_next c n m factory (nativeAt (ordinal+1))) :=
  ⟨actual_born_K observation nontrivial half depth ordinal n,
    actual_born_fixed_price observation nontrivial half depth ordinal n,
    actual_born_live observation nontrivial half depth ordinal n,
    actual_paid c n m factory (nativeAt (ordinal+1)),
    original_ledger c n m factory (nativeAt (ordinal+1)),
    original_occurrence c n m factory (nativeAt (ordinal+1)),
    input_from_original_receipt c n m factory (nativeAt (ordinal+1)),
    MR.increment_source (U.selected factory (nativeAt (ordinal+1)))
      (configuration c n m factory (nativeAt (ordinal+1))),
    source_trace_in_next_stock c n m factory (nativeAt (ordinal+1)),
    source_stock_written c n m factory (nativeAt (ordinal+1)),
    born_inventory c n m factory (nativeAt (ordinal+1)),
    actual_receipt_next c n m factory (nativeAt (ordinal+1)),
    whole_first c n m factory (nativeAt (ordinal+1)),
    generated_next c n m factory (nativeAt (ordinal+1))⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
