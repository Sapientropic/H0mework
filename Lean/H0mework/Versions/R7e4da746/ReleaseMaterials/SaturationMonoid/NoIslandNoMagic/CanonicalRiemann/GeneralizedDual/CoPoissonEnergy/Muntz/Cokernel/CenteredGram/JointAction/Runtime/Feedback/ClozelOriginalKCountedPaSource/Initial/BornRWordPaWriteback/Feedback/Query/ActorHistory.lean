import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.OperationDivision

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.ActorHistory
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private retainedCode from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private retainedValue from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRAdmissionPaidReadout
open private source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback
namespace Price
export BornRSourcePrice (inputAtPacket SourcePriceMethodReceipt actual_input_source)
end Price
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt)
end R
namespace Op
export OperationEffect (nativeInput nativeDecoder)
end Op
namespace Read
export OperationDivision (oldInput effectInput actual_R_query_operation_division)
end Read
attribute [local instance] baseGroups levelGroups
local notation "slot" => CompletedSourceRCalculation.Slot.branches
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half

private theorem project_zero (n : Nat) :
 M.wholeProjection n (0 : Lower.Value A.W n slot) = 0 := by
 induction n with
 | zero => rfl
 | succ n previous => exact previous

private theorem constant_input
 (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (value : Lower.Value A.W packet.1 slot)
 (literal : retainedCode packet.1 packet.2.1.1 =
  Expr.linear (-AddMonoidHom.id (Lower.Value A.W packet.1 slot))
   (Expr.linear (-AddMonoidHom.id (Lower.Value A.W packet.1 slot)) (.const value))) :
 Read.oldInput observation nontrivial half packet = Price.inputAtPacket packet ∧
 Read.effectInput observation nontrivial half packet = 0 := by
 have plain : ∀ rho : Env (Lower.Value A.W packet.1) A.X,
   (retainedCode packet.1 packet.2.1.1).eval rho = value := by
  intro rho
  rw [literal]
  simp only [Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, neg_neg]
 have plainEffect : ∀ rho delta : Env (Lower.Value A.W packet.1) A.X,
   (retainedCode packet.1 packet.2.1.1).effect rho delta = 0 := by
  intro rho delta
  rw [literal]
  simp only [Expr.effect, map_zero]
 have lifted : ∀ rho : Env (Lower.Value A.W (packet.1+1)) A.X,
   (Op.nativeInput packet.1 packet.2.1.1).eval rho =
    (value, (0 : Lower.Value A.W packet.1 slot)) := by
  intro rho
  exact (eval_liftExpr (Value := Lower.Value A.W packet.1)
   (retainedCode packet.1 packet.2.1.1)
   (fun target name => (rho target name).1) (fun target name => (rho target name).2)).trans
   (congrArg₂ Prod.mk (plain _) (plainEffect _ _))
 have liftedEffect : ∀ rho delta : Env (Lower.Value A.W (packet.1+1)) A.X,
   (Op.nativeInput packet.1 packet.2.1.1).effect rho delta = 0 := by
  intro rho delta
  have update := Expr.eval_update (Op.nativeInput packet.1 packet.2.1.1) rho delta
  rw [lifted (rho+delta), lifted rho] at update
  exact add_left_cancel (update.symm.trans (add_zero _).symm)
 constructor
 · unfold Read.oldInput Price.inputAtPacket retainedValue
   rw [lifted, plain]
   rfl
 · unfold Read.effectInput
   rw [liftedEffect]
   exact project_zero (packet.1+1)

/-- The local successor's literal retained syntax is read before choosing any later decoder. -/
private theorem successor_input
 (before after : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (grade : after.1 = before.1+1)
 (sourceAst : HEq (retainedCode after.1 after.2.1.1)
  (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W before.1) slot))
   (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W before.1) slot))
    (R.actualMaterial before.2.1.1 before.2.2.1).state.1))) :
 Read.oldInput observation nontrivial half after = Price.inputAtPacket after ∧
 Read.effectInput observation nontrivial half after = 0 := by
 rcases before with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 rcases after with ⟨m, ⟨nextFrame, nextSeed⟩, nextCfg, nextLanguage⟩
 change m = n+1 at grade
 cases grade
 let cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue := Lower.Value A.W n) (PhysicalVar := A.X) (sort := slot) :=
  ⟨A.X, datum, scalar, pair⟩
 let after : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot) :=
  ⟨n+1, ⟨nextFrame, nextSeed⟩, nextCfg, nextLanguage⟩
 let value := (R.actionResultAt frame cfg (S.actualOccurrence frame)).2.2.1
 have oldSyntax : retainedCode (n+1) nextFrame =
   Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W n) slot))
    (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W n) slot))
     (R.actualMaterial frame cfg).state.1) := eq_of_heq sourceAst
 have terminal := BornRActualHistoryConsumer.Generic.paid_expression frame cfg
 have literal : retainedCode (n+1) nextFrame =
   Expr.linear (-AddMonoidHom.id (Lower.Value A.W (n+1) slot))
    (Expr.linear (-AddMonoidHom.id (Lower.Value A.W (n+1) slot)) (.const value)) :=
  oldSyntax.trans (congrArg
   (fun expression : Expr (PairValue (Lower.Value A.W n)) A.X slot =>
    Expr.linear (-AddMonoidHom.id _) (Expr.linear (-AddMonoidHom.id _) expression)) terminal)
 exact constant_input observation nontrivial half after value literal

variable (depth ordinal : Nat)
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "packet" => D.packetAt factory initial programme rfl

private theorem canonical_input (update : Nat) :
 Read.oldInput observation nontrivial half (packet (update+1)) =
  M.actualStock observation nontrivial half depth ordinal update ∧
 Read.effectInput observation nontrivial half (packet (update+1)) = 0 := by
 have source := successor_input observation nontrivial half (packet update) (packet (update+1))
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions.packetAt_successor_grade
   factory initial programme rfl update)
  (BornRAdmissionStockLaw.actual_successor_retained observation nontrivial half depth ordinal update)
 exact ⟨source.1.trans (Price.actual_input_source observation nontrivial half depth ordinal update), source.2⟩

theorem at_method {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
 {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory} {update cutoff : Nat}
 (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index) (Whole := Whole)
  (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff) :
 Read.oldInput observation nontrivial half method.source =
  M.actualStock observation nontrivial half depth ordinal update ∧
 Read.effectInput observation nontrivial half method.source = 0 := by
 rw [method.source_literal]
 exact canonical_input observation nontrivial half depth ordinal update

variable (update cutoff : Nat)

/-- The original method occurrence and emitted history determine both actual decoder inputs. -/
theorem actual_decoder_actor_history :
 Read.oldInput observation nontrivial half (source observation nontrivial half depth ordinal update cutoff) =
  M.actualStock observation nontrivial half depth ordinal update ∧
 Read.effectInput observation nontrivial half (source observation nontrivial half depth ordinal update cutoff) = 0 ∧
 type_of% (installedMethod observation nontrivial half depth ordinal update cutoff).method.source_literal ∧
 type_of% (D.actual_index factory initial programme rfl (update+1)) ∧
 type_of% (D.history_end_index factory initial programme rfl update) ∧
 type_of% (Read.actual_R_query_operation_division observation nontrivial half depth ordinal update cutoff) := by
 have actor := at_method observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method
 exact ⟨actor.1, actor.2,
  (installedMethod observation nontrivial half depth ordinal update cutoff).method.source_literal,
  D.actual_index factory initial programme rfl (update+1),
  D.history_end_index factory initial programme rfl update,
  Read.actual_R_query_operation_division observation nontrivial half depth ordinal update cutoff⟩

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.ActorHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
