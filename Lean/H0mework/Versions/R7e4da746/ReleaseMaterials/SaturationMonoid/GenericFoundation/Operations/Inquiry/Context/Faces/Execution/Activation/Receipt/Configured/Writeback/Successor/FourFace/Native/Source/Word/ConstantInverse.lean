import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.ConstantTransport
import H0mework.Realization.Logic.SourceScope

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceOperationScalarInventoryLift SourceGeneratedScalarDifferentialResidual
namespace ActualSourceConstantInverse
namespace S
export ScalarRelationPresentation
  (RelationIndex relationMap relationMap_single freeEvaluation freeEvaluation_single freeEvaluation_naturality generatorMap)
end S
namespace O
export OriginalSourceConstantTransport
  (beforeTransport computedAfter actual_full_value actual_free_constants actual_old_free_constants
   computed_after original_whole_next)
end O
namespace F
export OriginalSourceConstantTransport.F (wholeFaces boundary)
end F
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (actualMaterial sourceWord words nextOriginFace nextFullValue next_full_value actual_updated_value
   next_old_constants request source_inverse whole_first canonical_next)
end SN

section Coefficients
variable {G : Type u} [AddCommGroup G]
private def coefficientWord (items : List (G × ℤ)) : G →₀ ℤ :=
  (items.map fun entry => Finsupp.single entry.1 entry.2).sum
private def coefficientValue (items : List (G × ℤ)) : G :=
  (items.map fun entry => entry.2 • entry.1).sum
-- Empty reduction retains the zero atom instead of silently discarding it.
private def coefficientRelations : List (G × ℤ) → (S.RelationIndex ℤ G →₀ ℤ)
  | [] => -Finsupp.single (.inr (0,0)) 1
  | (value,weight)::rest => -Finsupp.single (.inr (weight,value)) 1+
      coefficientRelations rest+
      Finsupp.single (.inl (weight • value,coefficientValue rest)) 1

private theorem coefficient_relations_read (items : List (G × ℤ)) :
    S.relationMap (R:=ℤ) G (coefficientRelations items)=
      coefficientWord items-Finsupp.single (coefficientValue items) 1 := by
  induction items with
  | nil =>
      simp [coefficientRelations,coefficientWord,coefficientValue,
        ScalarRelationPresentation.relation,ScalarRelationPresentation.scalarRelation]
  | cons entry rest previous =>
      rcases entry with ⟨value,weight⟩
      simp only [coefficientRelations,map_add,map_neg,S.relationMap_single,one_smul,previous,
        ScalarRelationPresentation.relation,ScalarRelationPresentation.scalarRelation,
        ScalarRelationPresentation.additionRelation,coefficientWord,coefficientValue,
        List.map_cons,List.sum_cons]
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      abel

private theorem coefficient_value_read (items : List (G × ℤ)) :
    S.freeEvaluation (R:=ℤ) G (coefficientWord items)=coefficientValue items := by
  induction items with
  | nil => exact map_zero _
  | cons entry rest previous =>
      change S.freeEvaluation (R:=ℤ) G
        (Finsupp.single entry.1 entry.2+coefficientWord rest)=entry.2 • entry.1+coefficientValue rest
      rw [map_add,S.freeEvaluation_single,previous]

private def coefficientItems (source : G →₀ ℤ) : List (G × ℤ) :=
  source.support.toList.map fun point => (point,source point)
omit [AddCommGroup G] in
private theorem coefficient_word_source (source : G →₀ ℤ) :
    coefficientWord (coefficientItems source)=source := by
  classical
  change ((source.support.toList.map fun point => (point,source point)).map
    (fun entry => Finsupp.single entry.1 entry.2)).sum=source
  rw [List.map_map]
  exact (Finset.sum_map_toList _ _).trans (Finsupp.sum_single source)

private def coefficientCertificate (source : G →₀ ℤ) : S.RelationIndex ℤ G →₀ ℤ :=
  coefficientRelations (coefficientItems source)
private theorem coefficient_certificate_read (source : G →₀ ℤ) :
    S.relationMap (R:=ℤ) G (coefficientCertificate source)=
      source-Finsupp.single (S.freeEvaluation (R:=ℤ) G source) 1 := by
  have generated:=coefficient_relations_read (coefficientItems source)
  rw [←coefficient_value_read,coefficient_word_source] at generated
  exact generated
end Coefficients

section ActualWord
variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target,AddCommGroup (V target)] {s : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value:=PairValue V) (Var:=X) (sort:=s))
variable (base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=PairValue V) (PhysicalVar:=X) (sort:=s))
variable (before : SourceInventoryExecutionFeed.Inventory (V:=V) (X:=X) (s:=s))
variable (oldEnvironment : Env V X)
variable (admissions : List (SourceInventoryExecutionFeed.AdmissionReceipt.Admission before
  (ActualNativeRelationTransport.AS.stockScalar frame base)))
local notation "material" => SN.actualMaterial frame base before oldEnvironment admissions
local notation "word" => SN.sourceWord frame base before admissions
local notation "face" => SN.nextOriginFace frame base before oldEnvironment admissions
local notation "G" => PairValue V s

def deltaTable : G →₀ ℤ :=
  O.computedAfter frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)-
    O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)

def actualValue : G := S.freeEvaluation (R:=ℤ) G (deltaTable frame base before oldEnvironment admissions)
def actualCertificate : S.RelationIndex ℤ G →₀ ℤ :=
  coefficientCertificate (deltaTable frame base before oldEnvironment admissions)

theorem actual_certificate :
    deltaTable frame base before oldEnvironment admissions-
      Finsupp.single (actualValue frame base before oldEnvironment admissions) 1=
    S.relationMap (R:=ℤ) G (actualCertificate frame base before oldEnvironment admissions) :=
  (coefficient_certificate_read _).symm

private abbrev Evidence (source : G →₀ ℤ) :=
  {certificate : S.RelationIndex ℤ G →₀ ℤ // S.relationMap (R:=ℤ) G certificate=
    source-Finsupp.single (S.freeEvaluation (R:=ℤ) G source) 1}

def actualInverse : SourceOperationLogic.ExistsEvidence (S.freeEvaluation (R:=ℤ) G) (Evidence (V:=V) (s:=s))
    (SourceOperationLogic.q (S.freeEvaluation (R:=ℤ) G)
      (Finsupp.single (actualValue frame base before oldEnvironment admissions) 1)) :=
  ⟨⟨deltaTable frame base before oldEnvironment admissions,
      (SourceOperationLogic.q_eq_iff _ _ _).mpr
        (ScalarRelationPresentation.relationRange_le_kernel (R:=ℤ) G
          ⟨actualCertificate frame base before oldEnvironment admissions,(actual_certificate _ _ _ _ _).symm⟩)⟩,
    actualCertificate frame base before oldEnvironment admissions,(actual_certificate _ _ _ _ _).symm⟩

def inverseData : Σ source : G →₀ ℤ, Evidence (V:=V) (s:=s) source :=
  SourceOperationLogic.existsEvidenceElim (S.freeEvaluation (R:=ℤ) G) (Evidence (V:=V) (s:=s))
    ⟨_,actualInverse frame base before oldEnvironment admissions⟩

theorem inverse_source : (inverseData frame base before oldEnvironment admissions).1=
    deltaTable frame base before oldEnvironment admissions := rfl

def restoredTable : G →₀ ℤ :=
  O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)+
    Finsupp.single (S.freeEvaluation (R:=ℤ) G (inverseData frame base before oldEnvironment admissions).1) 1+
    S.relationMap (R:=ℤ) G (inverseData frame base before oldEnvironment admissions).2.1

theorem restored_source : restoredTable frame base before oldEnvironment admissions=
    O.computedAfter frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word) := by
  have assemble (oldRead:G→₀ℤ) (data:Σ source:G→₀ℤ,Evidence (V:=V) (s:=s) source) :
      oldRead+Finsupp.single (S.freeEvaluation (R:=ℤ) G data.1) 1+
        S.relationMap (R:=ℤ) G data.2.1=oldRead+data.1 := by
    rw [data.2.2]
    abel
  unfold restoredTable
  refine (assemble
    (O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word))
    (inverseData frame base before oldEnvironment admissions)).trans ?_
  refine (congrArg (fun source=>
    O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)+source)
      (inverse_source frame base before oldEnvironment admissions)).trans ?_
  unfold deltaTable
  abel

theorem restored_next_constants : restoredTable frame base before oldEnvironment admissions=
    (face).rootRead.source.newConstants := by
  rw [restored_source,O.computed_after]
  exact O.actual_free_constants _ _ _ _ _

private theorem old_value : S.freeEvaluation (R:=ℤ) G
    (O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word))=
    (evaluation (R:=ℤ) oldEnvironment (SN.words frame base before admissions).sum,0) := by
  rw [O.actual_old_free_constants]
  let inclusion : V s →ₗ[ℤ] G := (LinearMap.id:V s→ₗ[ℤ]V s).prod (0:V s→ₗ[ℤ]V s)
  have natural:=LinearMap.congr_fun (S.freeEvaluation_naturality inclusion)
    (face).rootRead.source.oldConstants
  simp only [S.generatorMap,LinearMap.comp_apply] at natural
  change S.freeEvaluation (R:=ℤ) G
    (Finsupp.lmapDomain ℤ ℤ (fun value:V s=>(value,(0:V s)))
      (face).rootRead.source.oldConstants)=_ at natural
  rw [natural,SN.next_old_constants]
  have read:=LinearMap.congr_fun (valueMap_evaluation (R:=ℤ) oldEnvironment)
    (SN.words frame base before admissions).sum
  exact congrArg (fun value:V s=>(value,(0:V s))) read

theorem actual_paid_value : actualValue frame base before oldEnvironment admissions=
    (SN.request frame base before oldEnvironment admissions).input.expression.eval
      (SN.request frame base before oldEnvironment admissions).input.environment := by
  unfold actualValue deltaTable
  rw [map_sub]
  have generated:=O.actual_full_value frame base before oldEnvironment admissions
  change S.freeEvaluation (R:=ℤ) G (O.computedAfter frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word))=
    SN.nextFullValue frame base before oldEnvironment admissions at generated
  rw [generated,SN.next_full_value,old_value]
  exact (SN.actual_updated_value frame base before oldEnvironment admissions).symm

theorem actual_next_certificate :
    (face).rootRead.source.newConstants-
      O.beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)-
      Finsupp.single
        ((SN.request frame base before oldEnvironment admissions).input.expression.eval
          (SN.request frame base before oldEnvironment admissions).input.environment) 1=
      S.relationMap (R:=ℤ) G (actualCertificate frame base before oldEnvironment admissions) := by
  rw [←actual_paid_value]
  rw [←restored_next_constants,restored_source]
  exact actual_certificate frame base before oldEnvironment admissions

theorem actual_inverse_value : actualValue frame base before oldEnvironment admissions=
    (residualEquivRange (evaluation (R:=ℤ)
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input material).environment)
      (canonicalResidual (evaluation (R:=ℤ)
        (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input material).environment)
        (F.boundary material))).val :=
  (actual_paid_value frame base before oldEnvironment admissions).trans
    (SN.source_inverse frame base before oldEnvironment admissions).symm

def restoredFull : G := S.freeEvaluation (R:=ℤ) G (restoredTable frame base before oldEnvironment admissions)
theorem restored_full : restoredFull frame base before oldEnvironment admissions=
    OriginalSourceConstantTransport.realizedFull frame base before oldEnvironment admissions := by
  unfold restoredFull OriginalSourceConstantTransport.realizedFull
  rw [restored_source]

theorem original_whole_next :
    restoredTable frame base before oldEnvironment admissions=(face).rootRead.source.newConstants ∧
    (type_of% (O.original_whole_next frame base before oldEnvironment admissions)) :=
  ⟨restored_next_constants _ _ _ _ _,O.original_whole_next _ _ _ _ _⟩
end ActualWord

end ActualSourceConstantInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
