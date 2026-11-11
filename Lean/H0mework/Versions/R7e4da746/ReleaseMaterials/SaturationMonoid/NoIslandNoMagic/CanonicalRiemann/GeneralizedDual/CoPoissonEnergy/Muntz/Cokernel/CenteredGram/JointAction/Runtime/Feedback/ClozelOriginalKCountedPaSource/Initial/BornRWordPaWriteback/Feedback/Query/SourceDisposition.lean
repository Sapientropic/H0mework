import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.ActorHistory

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.SourceDisposition
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private produced_normalized from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport
open private retainedCode from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private after_native_retained from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRAdmissionStockLaw
open private bornGrade castWord from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Source
open private source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt)
end R
namespace Price
export BornRSourcePrice (SourcePriceMethodReceipt)
end Price

section ClosedSource
variable {S : Type} {V X : S → Type} [∀ s, AddCommGroup (V s)] {s : S}
variable {NW : WorldRelationNetwork} {Voc : Vocabulary}
variable {old : SourceNativeAuthoritativeRootClosure NW Voc} {origin : Voc.Current}
variable {original : Env V X} {operation : V s →+ V s} {input : Expr V X s}

/-- This cancels identical free value atoms before applying any scalar evaluator. -/
theorem produced_closed_values (data : Produced old origin original operation input) (value : V s)
 (closed : ∀ rho : Env V X, input.eval rho = value)
 (lifted : ∀ rho : Env (PairValue V) X, (liftExpr input).eval rho = (value, 0))
 (rho : Env (PairValue V) X) :
 valueMap (R := ℤ) rho (liftMap (R := ℤ) data.gamma) = 0 := by
 have paid : nu original operation input =
   Finsupp.single (operation value) 1 - Finsupp.single value 1 := by
  simp only [nu, omega, valueMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
   Finsupp.mapDomain_single, Expr.eval, closed]
 have liftedAction : (liftExpr (.linear operation input)).eval rho = (operation value, 0) := by
  change pairLinear operation ((liftExpr input).eval rho) = _
  rw [lifted rho]
  change (operation value, operation 0) = _
  rw [map_zero]
 have sourceValues : valueMap (R := ℤ) rho (liftMap (R := ℤ) (omega operation input)) =
   Finsupp.single (operation value, 0) 1 - Finsupp.single (value, 0) 1 := by
  simp only [omega, liftMap, valueMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
   Finsupp.mapDomain_single, liftedAction, lifted rho]
 have constantValues : valueMap (R := ℤ) rho
   (liftMap (R := ℤ) (constantMap (R := ℤ) (Var := X) (nu original operation input))) =
   Finsupp.single (operation value, 0) 1 - Finsupp.single (value, 0) 1 := by
  rw [paid]
  simp only [constantMap, liftMap, valueMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
   Finsupp.mapDomain_single, liftExpr, Expr.eval]
 rw [produced_normalized data]
 simp only [map_sub]
 rw [data.omega_source, data.nu_source, sourceValues, constantValues, sub_self]
end ClosedSource

attribute [local instance] baseGroups levelGroups
local notation "slot" => CompletedSourceRCalculation.Slot.branches
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half

private def ClosedInput
 (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) : Prop :=
 ∃ value : Lower.Value A.W packet.1 slot,
  retainedCode packet.1 packet.2.1.1 =
   Expr.linear (-AddMonoidHom.id (Lower.Value A.W packet.1 slot))
    (Expr.linear (-AddMonoidHom.id (Lower.Value A.W packet.1 slot)) (.const value))
attribute [local irreducible] ClosedInput

private theorem native_closed_values (n : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Lower.Value A.W n) (Var := A.X) (sort := slot))
 (value : Lower.Value A.W n slot)
 (literal : retainedCode n frame =
  Expr.linear (-AddMonoidHom.id (Lower.Value A.W n slot))
   (Expr.linear (-AddMonoidHom.id (Lower.Value A.W n slot)) (.const value)))
 (rho : Env (Lower.Value A.W (n+2)) A.X) :
 valueMap (R := ℤ) rho
  (liftMap (R := ℤ) (Value := Lower.Value A.W (n+1))
   (A.nativeWordData observation nontrivial half n frame).gamma) = 0 := by
 have closed : ∀ env : Env (Lower.Value A.W (n+1)) A.X,
   (liftExpr (Value := Lower.Value A.W n) (retainedCode n frame)).eval env =
    (value, (0 : Lower.Value A.W n slot)) := by
  intro env
  rw [literal]
  simp only [liftExpr, Expr.eval, pairLinear, AddMonoidHom.coe_prodMap, Prod.map_apply,
   AddMonoidHom.neg_apply, AddMonoidHom.id_apply, neg_neg, neg_zero]
 have lifted : ∀ env : Env (Lower.Value A.W (n+2)) A.X,
   (liftExpr (Value := Lower.Value A.W (n+1))
    (liftExpr (Value := Lower.Value A.W n) (retainedCode n frame))).eval env =
    ((value, (0 : Lower.Value A.W n slot)), (0 : Lower.Value A.W (n+1) slot)) := by
  intro env
  have effectClosed : ∀ base delta : Env (Lower.Value A.W (n+1)) A.X,
    (liftExpr (Value := Lower.Value A.W n) (retainedCode n frame)).effect base delta = 0 := by
   intro base delta
   have update := Expr.eval_update
    (liftExpr (Value := Lower.Value A.W n) (retainedCode n frame)) base delta
   rw [closed (base+delta), closed base] at update
   exact add_left_cancel (update.symm.trans (add_zero _).symm)
  exact (eval_liftExpr (Value := Lower.Value A.W (n+1))
   (liftExpr (Value := Lower.Value A.W n) (retainedCode n frame))
   (fun target name => (env target name).1) (fun target name => (env target name).2)).trans
   (congrArg₂ Prod.mk (closed _) (effectClosed _ _))
 exact produced_closed_values (A.nativeWordData observation nontrivial half n frame)
  (value, (0 : Lower.Value A.W n slot)) closed lifted rho

private theorem source_values_zero {m : Nat}
 (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) (grade : packet.1 = m)
 (word : Formal ℤ (Lower.Value A.W m) A.X slot)
 (closed : ∀ rho : Env (Lower.Value A.W (m+1)) A.X,
  valueMap (R := ℤ) rho (liftMap (R := ℤ) (Value := Lower.Value A.W m) word) = 0)
 (rho : Env (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar) :
 valueMap (R := ℤ) rho (Cfa.sourceWordAction packet (castWord grade.symm word)) = 0 := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 change n = m at grade
 cases grade
 exact closed rho

/-- The original constant source syntax pays the actual next query's full free value word. -/
theorem born_kappa_zero
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure)
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma)
 (value : Lower.Value A.W sourcePacket.1 slot)
 (literal : retainedCode sourcePacket.1 sourcePacket.2.1.1 =
  Expr.linear (-AddMonoidHom.id (Lower.Value A.W sourcePacket.1 slot))
   (Expr.linear (-AddMonoidHom.id (Lower.Value A.W sourcePacket.1 slot)) (.const value))) :
 kappa factory (AS.bornAfterNative (AS.nativeAfterAdmission factory sourcePacket))
  (nativeRelation (AS.nativeAfterAdmission factory sourcePacket) relation) = 0 := by
 rcases sourcePacket with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 let sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot) :=
  ⟨n, ⟨frame, seed⟩, ⟨A.X, datum, scalar, pair⟩, ⟨rfl⟩⟩
 let native := AS.nativeAfterAdmission factory sourcePacket
 let packet := AS.bornAfterNative native
 have grade : packet.1 = n+1 :=
  (bornGrade native).trans (ActualCofinalSourceAction.AS.nativeAfterAdmission_grade factory sourcePacket)
 have originalWord : relation.val = (A.nativeWordData observation nontrivial half n frame).gamma :=
  eq_of_heq generated
 have word : (nativeRelation native relation).val =
   castWord grade.symm (A.nativeWordData observation nontrivial half n frame).gamma := by
  change castWord grade.symm relation.val = _
  exact congrArg (castWord grade.symm) originalWord
 unfold kappa
 rw [word]
 exact source_values_zero packet grade (A.nativeWordData observation nontrivial half n frame).gamma
  (native_closed_values observation nontrivial half n frame value literal) (environment factory packet)

private theorem successor_literal
 (before after : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (grade : after.1 = before.1+1)
 (sourceAst : HEq (retainedCode after.1 after.2.1.1)
  (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W before.1) slot))
   (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W before.1) slot))
    (R.actualMaterial before.2.1.1 before.2.2.1).state.1))) : ClosedInput after := by
 unfold ClosedInput
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
 exact ⟨value, literal⟩

private theorem after_native_literal
 (before : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) :
 ClosedInput (AS.bornAfterNative (AS.nativeAfterAdmission factory before)) :=
 successor_literal before (AS.bornAfterNative (AS.nativeAfterAdmission factory before))
  ((bornGrade (AS.nativeAfterAdmission factory before)).trans
   (ActualCofinalSourceAction.AS.nativeAfterAdmission_grade factory before))
  (after_native_retained observation nontrivial half before)

variable (depth ordinal : Nat)
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "packet" => D.packetAt factory initial programme rfl

set_option maxHeartbeats 12000 in
theorem at_method {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
 {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory} {update cutoff : Nat}
 (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index) (Whole := Whole)
  (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff) : ClosedInput method.source :=
 Eq.mpr (congrArg ClosedInput (method.source_literal.trans
  (D.packetAt_successor factory initial programme rfl update)))
  (after_native_literal observation nontrivial half (packet update))

private theorem dispose_source
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure)
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma)
 (closed : ClosedInput sourcePacket) :
 kappa factory (AS.bornAfterNative (AS.nativeAfterAdmission factory sourcePacket))
  (nativeRelation (AS.nativeAfterAdmission factory sourcePacket) relation) = 0 := by
 unfold ClosedInput at closed
 obtain ⟨value, literal⟩ := closed
 exact born_kappa_zero observation nontrivial half sourcePacket relation generated value literal

attribute [local irreducible] installedMethod

variable (update cutoff : Nat)

set_option cleanup.letToHave false in
private theorem actual_literal : ClosedInput (source observation nontrivial half depth ordinal update cutoff) :=
 at_method observation nontrivial half depth ordinal
  (installedMethod observation nontrivial half depth ordinal update cutoff).method

theorem actual_kappa_zero :
 kappa factory
  (AS.bornAfterNative (AS.nativeAfterAdmission factory
   (source observation nontrivial half depth ordinal update cutoff)))
  (nativeRelation (AS.nativeAfterAdmission factory
   (source observation nontrivial half depth ordinal update cutoff))
   (actualBornRelation observation nontrivial half depth ordinal update cutoff).1) = 0 := by
 exact dispose_source observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff)
  (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
  ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
   (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))
  (actual_literal observation nontrivial half depth ordinal update cutoff)

set_option cleanup.letToHave false in
theorem actual_nu_actor_jump : type_of%
 ((actual_effect_source observation nontrivial half depth ordinal update cutoff).trans
  (congrArg₂ (fun left right : CompletedSourceRCalculation.Value slot => left-right)
   (installedMethod observation nontrivial half depth ordinal update cutoff).complete_R
   (installedMethod observation nontrivial half depth ordinal update cutoff).actual_source)) :=
 (actual_effect_source observation nontrivial half depth ordinal update cutoff).trans
  (congrArg₂ (fun left right : CompletedSourceRCalculation.Value slot => left-right)
   (installedMethod observation nontrivial half depth ordinal update cutoff).complete_R
   (installedMethod observation nontrivial half depth ordinal update cutoff).actual_source)

set_option cleanup.letToHave false in
/-- A paid query value word is discharged while its original R jump, prices and next remain live. -/
theorem actual_source_disposition :
 type_of% (actual_kappa_zero observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (actual_nu_actor_jump observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (actual_word_bill observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (actual_word_fee observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (M.actualStock_step observation nontrivial half depth ordinal update) ∧
 type_of% (ActorHistory.actual_decoder_actor_history observation nontrivial half depth ordinal update cutoff) :=
 ⟨actual_kappa_zero observation nontrivial half depth ordinal update cutoff,
  actual_nu_actor_jump observation nontrivial half depth ordinal update cutoff,
  actual_word_bill observation nontrivial half depth ordinal update cutoff,
  actual_word_fee observation nontrivial half depth ordinal update cutoff,
  M.actualStock_step observation nontrivial half depth ordinal update,
  ActorHistory.actual_decoder_actor_history observation nontrivial half depth ordinal update cutoff⟩

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.SourceDisposition
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
