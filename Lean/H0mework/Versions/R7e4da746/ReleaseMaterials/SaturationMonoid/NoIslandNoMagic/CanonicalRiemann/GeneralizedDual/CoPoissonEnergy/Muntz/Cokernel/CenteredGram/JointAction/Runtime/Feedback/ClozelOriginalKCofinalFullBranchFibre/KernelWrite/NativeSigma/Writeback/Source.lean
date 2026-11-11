import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Consumer
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement SourceGeneratedScalarDifferentialResidual
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open private liftExpr_remaining from H0mework.Realization.Operations.Execution.Coefficients.Words
namespace PA
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Action
 (sourceCursor sourceNextEnvironment secondEnvironment updatedPairEnvironment)
end PA
namespace Orbit
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame cursorAt)
end Orbit
namespace CI
export SourceOperationInquiry.Context.Installation (nextRawAt)
end CI
namespace Raw
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (raw_environment)
end Raw
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (query_word_read)
end Joint
namespace Stage
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (receiver nativeAfterAdmission_grade)
end Stage
namespace Input
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
 (HasActualInput actual_environment born_after_native_input native_after_admission_input withActualInput)
end Input
namespace NR
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input residual_value)
end NR
namespace Next
export BornInstalledJoint.MacroNext (bornPacket nextNative nextFrame nextSeed nextRootRead nextPhase next_phase)
end Next
namespace Dynamics
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
 (packet_next_active)
end Dynamics

section Physical
variable {V X : Unit → Type} [∀ target, AddCommGroup (V target)]
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := ()))

private theorem paid_of_credit (positive : 0 < remaining frame.event.state.1) :
 ∃ paid, frame.action = .inr paid := by
 cases actual : frame.action with
 | inr paid => exact ⟨paid, rfl⟩
 | inl settled =>
  have zero : remaining frame.event.state.1 = 0 := by rw [settled.2.down]; rfl
  omega

private theorem paired_environment_of_two_paid (credit : 2 ≤ remaining frame.event.state.1) :
 PA.updatedPairEnvironment (A.epoch frame) (S.actualOccurrence frame) =
 pairEnvironment frame.registered.input.environment 0 := by
 obtain ⟨first, firstActual⟩ := paid_of_credit frame (by omega)
 have debit := (congrArg (fun state => remaining state.1)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.mathNext_state frame)).trans
  (RootGeneratedDebtActivationJointSource.mathTarget_budget frame.event)
 obtain ⟨second, secondActual⟩ := paid_of_credit frame.mathNext (by omega)
 have source : PA.sourceNextEnvironment (A.epoch frame) (S.actualOccurrence frame) =
  frame.registered.input.environment := by
  change (CI.nextRawAt (A.epoch frame) (S.actualOccurrence frame)).environment = _
  unfold CI.nextRawAt
  have sourceAction : RootGeneratedDebtActivationJointSource.mathAction
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current.2 = .inr first := firstActual
  rw [sourceAction]
  rfl
 have cursor : PA.sourceCursor (A.epoch frame) (S.actualOccurrence frame) = Orbit.ofFrame frame := rfl
 have next : (Orbit.ofFrame frame).next = Orbit.ofFrame frame.mathNext := by
  unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
  have cursorAction : (Orbit.ofFrame frame).action = .inr first := firstActual
  rw [cursorAction]
  rfl
 have nextTwo : (Orbit.ofFrame frame.mathNext).next = Orbit.ofFrame frame.mathNext.mathNext := by
  unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
  have cursorAction : (Orbit.ofFrame frame.mathNext).action = .inr second := secondActual
  rw [cursorAction]
  rfl
 have secondEnv : PA.secondEnvironment (A.epoch frame) (S.actualOccurrence frame) =
  frame.registered.input.environment := by
  change (PA.sourceCursor (A.epoch frame) (S.actualOccurrence frame)).next.next.raw.environment = _
  rw [cursor, next, nextTwo]
  rfl
 unfold PA.updatedPairEnvironment
 rw [source, secondEnv, sub_self]

end Physical

section Word
variable {V X : Unit → Type} [∀ target, AddCommGroup (V target)]
private theorem word_effect_zero (old : Env V X) (word : Formal ℤ V X ()) :
 effectEvaluator (R := ℤ) old 0 word = 0 := by
 have zeroMap : effectEvaluator (R := ℤ) (s := ()) old 0 = 0 := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [effectEvaluator, Finsupp.linearCombination_single, Expr.effect_zero,
   smul_zero, LinearMap.zero_apply]
 exact (congrArg (fun map => map word) zeroMap).trans rfl

private theorem lift_word_zero (old : Env V X) (word : Formal ℤ V X ()) :
 evaluation (R := ℤ) (pairEnvironment old 0) (liftMap (R := ℤ) word) =
 (evaluation (R := ℤ) old word, 0) := by
 have generated := LinearMap.congr_fun (evaluation_liftMap (R := ℤ) old 0) word
 exact generated.trans (Prod.ext rfl (word_effect_zero old word))

private theorem paid_boundary_born_value
 (frame : A.M.Frame (Value := V) (Var := X) (sort := ()))
 (cfg : A.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := ())) :
 evaluation (R := ℤ) (B.born frame cfg).activeEnvironment (FF.boundary (AN.paid frame)) =
 ((FF.effectFaces (RB.transported frame cfg)).rangeEquiv
  (FF.paidCoordinate (RB.transported frame cfg))).val := by
 have generated := NR.residual_value (R := ℤ) (RB.transported frame cfg)
 change evaluation (R := ℤ) (NR.input (RB.transported frame cfg)).environment (FF.boundary (AN.paid frame)) =
  (N.expression (RB.transported frame cfg)).eval (NR.input (RB.transported frame cfg)).environment at generated
 rw [RB.actual_input] at generated
 exact generated.trans (RB.registered_inverse frame cfg).symm
end Word

local instance writebackGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private theorem code_budget (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (grade : Nat) :
 remaining (CF.codeAt code grade) = remaining code := by
 induction grade with
 | zero => rfl
 | succ grade previous =>
  exact (liftExpr_remaining (CF.codeAt code grade)).trans previous

private theorem native_credit (factory : NativeFactory) (packet : NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (codePositive : 0 < remaining code) :
 2 ≤ remaining (AS.nativeAfterAdmission factory packet).2.1.1.event.state.1 := by
 rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
   ⟨C.Var, datum, inventory, pairInventory⟩
  let packet : NativePacket := ⟨grade, data, cfg, ⟨rfl⟩⟩
  let receiver := (CA.nativePacket factory packet).2.1.1
  have raw : (R.actualMaterial data.1 cfg).raw = CF.codeAt code grade := by
   have source := (AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
    (generated data.1 (S.actualOccurrence data.1))
   exact congrArg (fun input => input.expression) source
  have budget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (R.actualMaterial data.1 cfg)
  have rawBudget := (congrArg remaining raw).trans (code_budget code grade)
  have registered := CA.receiver_ast factory packet
  have registeredBudget := (congrArg remaining registered).trans budget
  change remaining receiver.registered.input.expression = _ at registeredBudget
  have clock := SourceRegisteredClaimClock.remainder_generated receiver
  change remaining receiver.event.state.1 = remaining receiver.registered.input.expression - (0+1) at clock
  change 2 ≤ remaining receiver.event.state.1
  omega

private theorem native_raw_environment (factory : NativeFactory) (packet : NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (codePositive : 0 < remaining code) :
 (PR.raw (AS.nativeAfterAdmission factory packet).2.1.2
  (A.epoch (AS.nativeAfterAdmission factory packet).2.1.1)
  (S.actualOccurrence (AS.nativeAfterAdmission factory packet).2.1.1)).environment =
 pairEnvironment (AS.nativeAfterAdmission factory packet).2.1.1.registered.input.environment 0 :=
 (Raw.raw_environment _ _ _).trans
  (paired_environment_of_two_paid _ (native_credit factory packet code generated codePositive))

def admissionValue (factory : NativeFactory) (packet : NativePacket)
 (value : PairValue (L.Value (PairValue C.Value) packet.1) ()) :
 L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 () :=
 Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ())
  (AS.nativeAfterAdmission_grade factory packet).symm) value

def admissionWord (factory : NativeFactory) (packet : NativePacket)
 : Formal ℤ (PairValue (L.Value (PairValue C.Value) packet.1)) C.Var () →ₗ[ℤ]
 Formal ℤ (L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1) C.Var () :=
 Eq.mp (congrArg (fun grade =>
  Formal ℤ (PairValue (L.Value (PairValue C.Value) packet.1)) C.Var () →ₗ[ℤ]
   Formal ℤ (L.Value (PairValue C.Value) grade) C.Var ())
  (AS.nativeAfterAdmission_grade factory packet).symm) LinearMap.id

def receiptSelected (native : NativePacket) :
 A.M.Frame (Value := L.Value (PairValue C.Value) native.1) (Var := C.Var) (sort := ()) :=
 S.Complete.atReceipt (AS.stockCfg native.2.2.1) native.2.1.1 0

def nativeBoundary (native : NativePacket) : Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var () :=
 FF.boundary (AN.paid (receiptSelected native))

def nativeInverseValue (native : NativePacket) : L.Value (PairValue C.Value) native.1 () :=
 ((FF.effectFaces (RB.transported (receiptSelected native) native.2.2.1)).rangeEquiv
  (FF.paidCoordinate (RB.transported (receiptSelected native) native.2.2.1))).val

private theorem born_grade (native : NativePacket) : (AS.bornAfterNative native).1 = native.1 := rfl

def bornValue (native : NativePacket) (value : L.Value (PairValue C.Value) native.1 ()) :
 L.Value (PairValue C.Value) (AS.bornAfterNative native).1 () :=
 Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ()) (born_grade native).symm) value

def bornWord (native : NativePacket) : Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var () →ₗ[ℤ]
 Formal ℤ (L.Value (PairValue C.Value) (AS.bornAfterNative native).1) C.Var () :=
 Eq.mp (congrArg (fun grade => Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var () →ₗ[ℤ]
  Formal ℤ (L.Value (PairValue C.Value) grade) C.Var ()) (born_grade native).symm) LinearMap.id

private theorem native_born_value (native : NativePacket) :
 evaluation (R := ℤ) (AS.bornAfterNative native).2.1.1.activeEnvironment
  (bornWord native (nativeBoundary native)) = bornValue native (nativeInverseValue native) :=
 paid_boundary_born_value (receiptSelected native) native.2.2.1

private theorem native_input_word (factory : NativeFactory) (packet : NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
 evaluation (R := ℤ) (AS.nativeAfterAdmission factory packet).2.1.1.registered.input.environment
  (admissionWord factory packet (liftMap (R := ℤ) word)) =
 admissionValue factory packet
  (evaluation (R := ℤ) (S.next packet.2.1.1 packet.2.2.1).activeEnvironment word, 0) := by
 rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
   ⟨C.Var, datum, inventory, pairInventory⟩
  have after := (AS.stock_action_reader (S.next data.1 cfg) cfg (S.actualOccurrence (S.next data.1 cfg))).symm.trans
   (generated (S.next data.1 cfg) (S.actualOccurrence (S.next data.1 cfg)))
  have afterEnvironment := congrArg (fun input => input.environment) after
  have actual := (add_sub_cancel (R.actualMaterial data.1 cfg).environment
   (SourceGeneratedInquiryReceiptAction.afterEnvironment data.1 cfg)).trans
   (afterEnvironment.trans (congrArg (fun env => pairEnvironment env (0 : Env (L.Value (PairValue C.Value) grade) C.Var))
    (Input.actual_environment grade (S.next data.1 cfg))))
  change evaluation (R := ℤ) (NR.input (R.actualMaterial data.1 cfg)).environment (liftMap (R := ℤ) word) =
   (evaluation (R := ℤ) (S.next data.1 cfg).activeEnvironment word, 0)
  exact (congrArg (fun env => evaluation (R := ℤ) env (liftMap (R := ℤ) word)) actual).trans
   (lift_word_zero (S.next data.1 cfg).activeEnvironment word)

private theorem native_joint_word (factory : NativeFactory) (packet : NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (codePositive : 0 < remaining code)
 (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
 (J.face (AS.nativeAfterAdmission factory packet).2.1.2
  (A.epoch (AS.nativeAfterAdmission factory packet).2.1.1)
  (S.actualOccurrence (AS.nativeAfterAdmission factory packet).2.1.1)).freeEvaluation
  (liftMap (R := ℤ) (admissionWord factory packet (liftMap (R := ℤ) word))) =
 (admissionValue factory packet
  (evaluation (R := ℤ) (S.next packet.2.1.1 packet.2.2.1).activeEnvironment word, 0), 0) := by
 rw [Joint.query_word_read]
 rw [native_raw_environment factory packet code generated codePositive]
 exact (lift_word_zero _ _).trans
  (congrArg (fun value => (value, 0)) (native_input_word factory packet code generated word))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def nativeFace (native : NativePacket) :=
 J.face (PhysicalValue := L.Value (PairValue C.Value) native.1) (PhysicalVar := C.Var) (sort := ())
  native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1)

def nativeEvaluation (native : NativePacket) :
 Formal ℤ (PairValue (L.Value (PairValue C.Value) native.1)) C.Var () →ₗ[ℤ]
 PairValue (L.Value (PairValue C.Value) native.1) () :=
 (nativeFace native).freeEvaluation

def retainedInNative (factory : NativeFactory) (packet : NativePacket)
 (value : L.Value (PairValue C.Value) packet.1 ()) :
 L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 () := admissionValue factory packet (value, 0)

def retainedPair (factory : NativeFactory) (packet : NativePacket)
 (value : L.Value (PairValue C.Value) packet.1 ()) :
 PairValue (L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1) () :=
 (retainedInNative factory packet value, 0)

abbrev nextSigmaWord := liftMap (R := ℤ)
 (admissionWord (D.factory observation nontrivial half) (Next.bornPacket observation nontrivial half depth ordinal)
  (liftMap (R := ℤ) (bornWord (originalNative observation nontrivial half depth ordinal)
   (nativeBoundary (originalNative observation nontrivial half depth ordinal)))))
abbrev nextFace := nativeFace (Next.nextNative observation nontrivial half depth ordinal)
abbrev retainedValue := retainedInNative (D.factory observation nontrivial half)
 (Next.bornPacket observation nontrivial half depth ordinal)
 (bornValue (originalNative observation nontrivial half depth ordinal)
  (nativeInverseValue (originalNative observation nontrivial half depth ordinal)))

private theorem native_sigma_next_evaluator
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (factory : NativeFactory) (packet : NativePacket) (positive : 0 < remaining code) :
 let actualFactory := Input.withActualInput code factory
 let native := AS.nativeAfterAdmission actualFactory packet
 let born := AS.bornAfterNative native
 nativeEvaluation (AS.nativeAfterAdmission actualFactory born)
  (liftMap (R := ℤ) (admissionWord actualFactory born
   (liftMap (R := ℤ) (bornWord native (nativeBoundary native))))) =
 retainedPair actualFactory born (bornValue native (nativeInverseValue native)) := by
 dsimp only
 let actualFactory := Input.withActualInput code factory
 let native := AS.nativeAfterAdmission actualFactory packet
 let born := AS.bornAfterNative native
 have input := Input.born_after_native_input code native
  (Input.native_after_admission_input code factory packet)
 have generated := native_joint_word actualFactory born code input positive
  (bornWord native (nativeBoundary native))
 have source := Dynamics.packet_next_active actualFactory packet
 have inverse := native_born_value native
 exact generated.trans (congrArg (retainedPair actualFactory born)
  ((congrArg (fun env => evaluation (R := ℤ) env
   (bornWord native (nativeBoundary native))) source).trans inverse))

/-- The actual next primary Joint reads this same full native receipt before grade collapse. -/
theorem original_sigma_next_evaluator : type_of%
 (native_sigma_next_evaluator (FR.jointCode (RSource.code observation nontrivial half))
  (SF.defaultFactory (PairValue C.Value) C.Var ())
  (originalPredecessor observation nontrivial half depth ordinal) (by change 0 < 4; omega)) :=
 native_sigma_next_evaluator (FR.jointCode (RSource.code observation nontrivial half))
  (SF.defaultFactory (PairValue C.Value) C.Var ())
  (originalPredecessor observation nontrivial half depth ordinal) (by change 0 < 4; omega)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
