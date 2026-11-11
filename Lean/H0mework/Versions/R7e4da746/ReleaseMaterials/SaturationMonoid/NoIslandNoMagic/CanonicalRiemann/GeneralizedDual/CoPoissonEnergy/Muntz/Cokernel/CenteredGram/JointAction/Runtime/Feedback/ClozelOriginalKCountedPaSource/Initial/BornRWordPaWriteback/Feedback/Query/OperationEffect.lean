import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.OperationEffect
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private produced_normalized from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport
open private retainedCode pairAction from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private wholeProjection_add from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSealedMethodHistory
open private bornGrade castWord from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Source
open private source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback

section Produced
variable {S : Type} {V X : S → Type} [∀ s, AddCommGroup (V s)] {s : S}
variable {NW : WorldRelationNetwork} {Voc : Vocabulary}
variable {old : SourceNativeAuthoritativeRootClosure NW Voc} {origin : Voc.Current}
variable {original : Env V X} {operation : V s →+ V s} {input : Expr V X s}

private theorem effect_constant (rho delta : Env V X) (nu : V s →₀ ℤ) :
 effectEvaluator (R := ℤ) rho delta (constantMap (R := ℤ) (Var := X) nu) = 0 := by
 have killed : (effectEvaluator (R := ℤ) (s := s) rho delta).comp
   (constantMap (R := ℤ)) = 0 := by
  apply Finsupp.lhom_ext
  intro value coefficient
  simp only [LinearMap.comp_apply, constantMap, Finsupp.lmapDomain_apply,
   Finsupp.mapDomain_single, effectEvaluator, Finsupp.linearCombination_single,
   Expr.effect, smul_zero, LinearMap.zero_apply]
 exact LinearMap.congr_fun killed nu

/-- The complete source relation retains both its historical value debt and its new effect. -/
theorem produced_operation_effect (data : Produced old origin original operation input)
 (rho delta : Env V X) :
 input.eval rho +
  (evaluation (R := ℤ) (pairEnvironment rho delta) (liftMap (R := ℤ) data.gamma)).1 +
  ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s) data.nu =
  operation (input.eval rho) ∧
 input.effect rho delta +
  (evaluation (R := ℤ) (pairEnvironment rho delta) (liftMap (R := ℤ) data.gamma)).2 =
  operation (input.effect rho delta) := by
 have lifted : evaluation (R := ℤ) (pairEnvironment rho delta) (liftMap (R := ℤ) data.gamma) =
   (evaluation (R := ℤ) rho data.gamma, effectEvaluator (R := ℤ) rho delta data.gamma) :=
  LinearMap.congr_fun (evaluation_liftMap (R := ℤ) (s := s) rho delta) data.gamma
 have normalized := produced_normalized data
 have oldRead : evaluation (R := ℤ) rho data.gamma =
   operation (input.eval rho) - input.eval rho -
    ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s) data.nu := by
  have constant : evaluation (R := ℤ) rho (constantMap (R := ℤ) (Var := X) data.nu) =
    ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s) data.nu :=
   LinearMap.congr_fun (evaluation_constantMap (R := ℤ) (s := s) rho) data.nu
  rw [normalized, map_sub, constant, data.omega_source]
  simp only [omega, map_sub, evaluation, Finsupp.linearCombination_single, one_smul, Expr.eval]
 have effectRead : effectEvaluator (R := ℤ) rho delta data.gamma =
   operation (input.effect rho delta) - input.effect rho delta := by
  rw [normalized, map_sub, effect_constant, sub_zero, data.omega_source]
  simp only [omega, map_sub, effectEvaluator, Finsupp.linearCombination_single, one_smul, Expr.effect]
 rw [lifted, oldRead, effectRead]
 constructor
 · rw [add_assoc, sub_add_cancel, ← add_sub_assoc, add_sub_cancel_left]
 · rw [← add_sub_assoc, add_sub_cancel_left]
end Produced

attribute [local instance] baseGroups levelGroups
local notation "slot" => CompletedSourceRCalculation.Slot.branches
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half

def nativeInput (n : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Lower.Value A.W n) (Var := A.X) (sort := slot)) :
 Expr (Lower.Value A.W (n+1)) A.X slot :=
 liftExpr (Value := Lower.Value A.W n) (retainedCode n frame)

/-- Each outer old/effect channel is projected separately; the full quartet stays intact. -/
theorem native_operation_effect (n : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Lower.Value A.W n) (Var := A.X) (sort := slot))
 (rho delta : Env (Lower.Value A.W (n+1)) A.X) :
 let data := A.nativeWordData observation nontrivial half n frame
 let K := evaluation (R := ℤ) (pairEnvironment rho delta) (liftMap (R := ℤ) data.gamma)
 let a := M.wholeProjection (n+1) ((nativeInput n frame).eval rho)
 let d := M.wholeProjection (n+1) ((nativeInput n frame).effect rho delta)
 let N := M.wholeProjection (n+1)
  (ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (n+1) slot) data.nu)
 a + M.wholeProjection (n+1) K.1 + N =
  OriginalKFullSourceRAction.variableAction observation nontrivial half a ∧
 d + M.wholeProjection (n+1) K.2 =
  OriginalKFullSourceRAction.variableAction observation nontrivial half d := by
 dsimp only
 have generated := produced_operation_effect
  (A.nativeWordData observation nontrivial half n frame) rho delta
 constructor
 · have projected := congrArg (M.wholeProjection (n+1)) generated.1
   rw [wholeProjection_add, wholeProjection_add] at projected
   exact projected.trans (M.wholeProjection_action observation nontrivial half n
    ((nativeInput n frame).eval rho).1)
 · have projected := congrArg (M.wholeProjection (n+1)) generated.2
   rw [wholeProjection_add] at projected
   exact projected.trans (M.wholeProjection_action observation nontrivial half n
    ((nativeInput n frame).effect rho delta).1)

private theorem decoderGrade
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) :
 (AS.bornAfterNative (AS.nativeAfterAdmission factory sourcePacket)).1 + 1 = sourcePacket.1 + 2 :=
 congrArg (fun grade => grade+1)
  ((bornGrade (AS.nativeAfterAdmission factory sourcePacket)).trans
   (ActualCofinalSourceAction.AS.nativeAfterAdmission_grade factory sourcePacket))

private def castEnvironment {m n : Nat} (grade : m = n)
 {Y Z : CompletedSourceRCalculation.Slot → Type} (language : Y = Z)
 (rho : Env (Lower.Value A.W m) Y) : Env (Lower.Value A.W n) Z := by
 cases grade
 cases language
 exact rho

private theorem source_eval_cast {m : Nat}
 (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (grade : packet.1 = m)
 (rho : Env (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar)
 (word : Formal ℤ (Lower.Value A.W m) A.X slot) :
 (congrArg (fun level => level+1) grade ▸
   evaluation (R := ℤ) rho (Cfa.sourceWordAction packet (castWord grade.symm word))) =
 evaluation (R := ℤ)
  (castEnvironment (congrArg (fun level => level+1) grade) packet.2.2.2.down rho)
  (liftMap (R := ℤ) (Value := Lower.Value A.W m) word) := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 change n = m at grade
 cases grade
 rfl

/-- This is the actual query decoder, with only its original grade/language equalities eliminated. -/
def nativeDecoder
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) :
 Env (Lower.Value A.W (sourcePacket.1+2)) A.X :=
 let packet := AS.bornAfterNative (AS.nativeAfterAdmission factory sourcePacket)
 castEnvironment (decoderGrade observation nontrivial half sourcePacket) packet.2.2.2.down
  (environment factory packet)

def bornQueryValue
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure) :
 Lower.Value A.W (sourcePacket.1+2) slot :=
 let native := AS.nativeAfterAdmission factory sourcePacket
 let packet := AS.bornAfterNative native
 decoderGrade observation nontrivial half sourcePacket ▸
  ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (packet.1+1) slot)
   (kappa factory packet (nativeRelation native relation))

/-- Same-source word identity, rather than an equality between completed receiver values. -/
theorem born_query_value
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure)
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma) :
 bornQueryValue observation nontrivial half sourcePacket relation =
 evaluation (R := ℤ) (nativeDecoder observation nontrivial half sourcePacket)
  (liftMap (R := ℤ) (Value := Lower.Value A.W (sourcePacket.1+1)) (Var := A.X)
   (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma) := by
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
 have read : ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (packet.1+1) slot)
    (kappa factory packet (nativeRelation native relation)) =
   evaluation (R := ℤ) (environment factory packet)
    (Cfa.sourceWordAction packet (nativeRelation native relation).val) :=
  LinearMap.congr_fun (valueMap_evaluation (R := ℤ) (s := slot) (environment factory packet)) _
 have word : (nativeRelation native relation).val =
   castWord grade.symm (A.nativeWordData observation nontrivial half n frame).gamma := by
  change castWord grade.symm relation.val = _
  exact congrArg (castWord grade.symm) originalWord
 rw [word] at read
 have paid := congrArg
  (fun value : Lower.Value A.W (packet.1+1) slot => congrArg (fun level => level+1) grade ▸ value) read
 exact paid.trans (source_eval_cast packet grade (environment factory packet)
  (A.nativeWordData observation nontrivial half n frame).gamma)

/-- The actual admitted query supplies the two complete quartet operation equations. -/
theorem born_operation_effect
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure)
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma) :
 let n := sourcePacket.1
 let frame := sourcePacket.2.1.1
 let E := nativeDecoder observation nontrivial half sourcePacket
 let rho := fun target name => (E target name).1
 let delta := fun target name => (E target name).2
 let K := bornQueryValue observation nontrivial half sourcePacket relation
 let data := A.nativeWordData observation nontrivial half n frame
 let a := M.wholeProjection (n+1) ((nativeInput n frame).eval rho)
 let d := M.wholeProjection (n+1) ((nativeInput n frame).effect rho delta)
 let N := M.wholeProjection (n+1)
  (ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (n+1) slot) data.nu)
 a + M.wholeProjection (n+1) K.1 + N =
  OriginalKFullSourceRAction.variableAction observation nontrivial half a ∧
 d + M.wholeProjection (n+1) K.2 =
  OriginalKFullSourceRAction.variableAction observation nontrivial half d := by
 dsimp only
 rw [born_query_value observation nontrivial half sourcePacket relation generated]
 exact native_operation_effect observation nontrivial half sourcePacket.1 sourcePacket.2.1.1
  (fun target name => (nativeDecoder observation nontrivial half sourcePacket target name).1)
  (fun target name => (nativeDecoder observation nontrivial half sourcePacket target name).2)

variable (depth ordinal update cutoff : Nat)

theorem actual_R_query_operation_effect : type_of%
 (born_operation_effect observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff)
  (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
  ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
   (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))) :=
 born_operation_effect observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff)
  (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
  ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
   (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.OperationEffect
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
