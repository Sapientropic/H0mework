import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceOperationScalarInventoryLift
open SourceGeneratedScalarDifferentialResidual
namespace OriginalSourceConstantTransport
namespace Scalar
export ScalarRelationPresentation (RelationIndex additionRelation relation relationMap freeEvaluation)
end Scalar
namespace Dual
export SourceGeneratedCompleteWordDual (pairing single injective coimageRecovery recovery_source)
end Dual
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (input expression relation_boundary updated_value residual_value)
end N
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
  (wholeFaces wholeInput boundary actualRelation complex generated_differential whole_recovery
   actual_inverse actual_effect effectFaces paidCoordinate)
end F
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (actualMaterial sourceWord words afterEnvironment request_environment nextOriginFace next_new_constants
   next_old_constants next_full_value next_full_certificate nextFullValue source_effect source_inverse whole_first canonical_next)
end SN

section ActualUpdate
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {sort : S}
variable (old increment : Env Value Var)

def effectValueMap : Formal ℤ Value Var sort →ₗ[ℤ] (Value sort →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun expression => expression.effect old increment)

/-- The source operation supplies both entries of every integer addition relation. -/
def additionCertificate : Formal ℤ Value Var sort →ₗ[ℤ]
    (Scalar.RelationIndex ℤ (Value sort) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun expression =>
    Sum.inl (expression.eval old,expression.effect old increment))

theorem constant_update :
    valueMap (R:=ℤ) old+effectValueMap (sort:=sort) old increment-
      valueMap (R:=ℤ) (old+increment)=
    (Scalar.relationMap (R:=ℤ) (Value sort)).comp (additionCertificate old increment) := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    valueMap,effectValueMap,additionCertificate,Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single,ScalarRelationPresentation.relationMap_single,
    ScalarRelationPresentation.relation,ScalarRelationPresentation.additionRelation]
  rw [Expr.eval_update]
  simp only [smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem detector_update (word : Formal ℤ Value Var sort) (detector : Value sort →₀ ℤ) :
    Dual.pairing (valueMap (R:=ℤ) (old+increment) word) detector=
      Dual.pairing (valueMap (R:=ℤ) old word) detector+
      Dual.pairing (effectValueMap old increment word) detector-
      Dual.pairing (Scalar.relationMap (R:=ℤ) (Value sort)
        (additionCertificate old increment word)) detector := by
  have generated:=LinearMap.congr_fun (constant_update (sort:=sort) old increment) word
  have paired:=congrArg (fun value:Value sort →₀ ℤ=>Dual.pairing value detector) generated
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,map_add,map_sub] at paired
  omega

theorem effect_realization :
    (Scalar.freeEvaluation (R:=ℤ) (Value sort)).comp (effectValueMap (sort:=sort) old increment)=
      effectEvaluator (R:=ℤ) old increment := by
  unfold effectValueMap ScalarRelationPresentation.freeEvaluation effectEvaluator
  rw [Finsupp.linearCombination_comp_lmapDomain]
  rfl

private theorem lifted_old_constants (old : Env Value Var) :
    (valueMap (R:=ℤ) (s:=sort) (pairEnvironment old 0)).comp (liftMap (R:=ℤ))=
      (Finsupp.lmapDomain ℤ ℤ (fun value:Value sort=>(value,(0:Value sort)))).comp
        (valueMap (R:=ℤ) old) := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.comp_apply,valueMap,liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    eval_liftExpr,Expr.effect_zero]
end ActualUpdate

section OriginalWord
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
local notation "originFace" => SN.nextOriginFace frame base before oldEnvironment admissions
local notation "word" => SN.sourceWord frame base before admissions

abbrev Whole := UnifiedFourFace.Perfectification (F.wholeInput material)
abbrev recover : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    Formal ℤ (PairValue V) X s := Dual.coimageRecovery

def beforeTransport : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    (PairValue V s →₀ ℤ) :=
  (valueMap (R:=ℤ) (material).environment).comp (recover frame base before oldEnvironment admissions)

def afterTransport : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    (PairValue V s →₀ ℤ) :=
  (valueMap (R:=ℤ) (N.input material).environment).comp (recover frame base before oldEnvironment admissions)

def effectTransport : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    (PairValue V s →₀ ℤ) :=
  (effectValueMap (material).environment (material).increment).comp
    (recover frame base before oldEnvironment admissions)

def correctionTransport : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    (PairValue V s →₀ ℤ) :=
  ((Scalar.relationMap (R:=ℤ) (PairValue V s)).comp
    (additionCertificate (material).environment (material).increment)).comp
      (recover frame base before oldEnvironment admissions)

/-- Only the original old state and its actual operation effect construct the next table. -/
def computedAfter : Whole frame base before oldEnvironment admissions →ₗ[ℤ]
    (PairValue V s →₀ ℤ) :=
  beforeTransport frame base before oldEnvironment admissions+
    effectTransport frame base before oldEnvironment admissions-
    correctionTransport frame base before oldEnvironment admissions

/-- No relation is removed when the source's whole word crosses the actual environment update. -/
theorem actual_transport (value : Whole frame base before oldEnvironment admissions) :
    beforeTransport frame base before oldEnvironment admissions value+
      effectTransport frame base before oldEnvironment admissions value-
      afterTransport frame base before oldEnvironment admissions value=
    correctionTransport frame base before oldEnvironment admissions value :=
  LinearMap.congr_fun (constant_update (material).environment (material).increment)
    (recover frame base before oldEnvironment admissions value)

theorem computed_after : computedAfter frame base before oldEnvironment admissions=
    afterTransport frame base before oldEnvironment admissions := by
  apply LinearMap.ext
  intro value
  have source:=actual_transport frame base before oldEnvironment admissions value
  change beforeTransport frame base before oldEnvironment admissions value+
    effectTransport frame base before oldEnvironment admissions value-
    correctionTransport frame base before oldEnvironment admissions value=_
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp source).trans (add_comm _ _))

theorem actual_detector (value : Whole frame base before oldEnvironment admissions)
    (detector : PairValue V s →₀ ℤ) :
    Dual.pairing (afterTransport frame base before oldEnvironment admissions value) detector=
      Dual.pairing (beforeTransport frame base before oldEnvironment admissions value) detector+
      Dual.pairing (effectTransport frame base before oldEnvironment admissions value) detector-
      Dual.pairing (correctionTransport frame base before oldEnvironment admissions value) detector :=
  detector_update (material).environment (material).increment
    (recover frame base before oldEnvironment admissions value) detector

theorem actual_free_constants :
    afterTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)=
      (originFace).rootRead.source.newConstants := by
  change valueMap (R:=ℤ) (N.input material).environment
    (Dual.coimageRecovery ((F.wholeFaces material).canonical word))=_
  rw [F.whole_recovery]
  change valueMap (R:=ℤ) ((material).environment+(material).increment) word=_
  rw [show (material).environment+(material).increment=SN.afterEnvironment frame base from
    SN.request_environment frame base before oldEnvironment admissions]
  exact (SN.next_new_constants frame base before oldEnvironment admissions).symm

theorem actual_old_free_constants :
    beforeTransport frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word)=
      Finsupp.lmapDomain ℤ ℤ (fun value:V s=>(value,(0:V s)))
        (originFace).rootRead.source.oldConstants := by
  change valueMap (R:=ℤ) (material).environment
    (Dual.coimageRecovery ((F.wholeFaces material).canonical word))=_
  rw [F.whole_recovery,SN.next_old_constants]
  exact LinearMap.congr_fun (lifted_old_constants (sort:=s) oldEnvironment)
    (SN.words frame base before admissions).sum

def realizedFull : PairValue V s := Scalar.freeEvaluation (R:=ℤ) (PairValue V s)
  (computedAfter frame base before oldEnvironment admissions ((F.wholeFaces material).canonical word))

theorem actual_full_value : realizedFull frame base before oldEnvironment admissions=
    SN.nextFullValue frame base before oldEnvironment admissions := by
  unfold realizedFull
  rw [computed_after,actual_free_constants]
  exact (SN.next_full_certificate frame base before oldEnvironment admissions).symm

private theorem correction_realization_zero (value : Whole frame base before oldEnvironment admissions) :
    Scalar.freeEvaluation (R:=ℤ) (PairValue V s)
      (correctionTransport frame base before oldEnvironment admissions value)=0 :=
  ScalarRelationPresentation.relationRange_le_kernel (R:=ℤ) (PairValue V s) ⟨_,rfl⟩

/-- The existing inverse fibre consumes the integer mixed action of its own full cochain boundary. -/
theorem actual_inverse : Scalar.freeEvaluation (R:=ℤ) (PairValue V s)
    (computedAfter frame base before oldEnvironment admissions
      ((F.wholeFaces material).canonical
        (((F.complex material).d 0 1).hom (F.actualRelation material)).val)-
      beforeTransport frame base before oldEnvironment admissions
        ((F.wholeFaces material).canonical
          (((F.complex material).d 0 1).hom (F.actualRelation material)).val))=
    (residualEquivRange (evaluation (R:=ℤ) (N.input material).environment)
      (canonicalResidual (evaluation (R:=ℤ) (N.input material).environment) (F.boundary material))).val := by
  rw [F.generated_differential]
  have action : ∀ value,computedAfter frame base before oldEnvironment admissions value-
      beforeTransport frame base before oldEnvironment admissions value=
      effectTransport frame base before oldEnvironment admissions value-
      correctionTransport frame base before oldEnvironment admissions value := by
    intro value
    unfold computedAfter
    simp only [LinearMap.add_apply,LinearMap.sub_apply]
    abel
  rw [action,map_sub,correction_realization_zero,sub_zero]
  change Scalar.freeEvaluation (R:=ℤ) (PairValue V s)
    (effectValueMap (material).environment (material).increment
      (Dual.coimageRecovery ((F.wholeFaces material).canonical (F.boundary material))))=_
  rw [F.whole_recovery]
  have generated:=LinearMap.congr_fun (effect_realization (material).environment (material).increment)
    (F.boundary material)
  exact generated.trans ((SN.source_effect frame base before oldEnvironment admissions).symm.trans
    (SN.source_inverse frame base before oldEnvironment admissions).symm)

theorem original_whole_next :
    (type_of% (SN.whole_first frame base before oldEnvironment admissions)) ∧
      (type_of% (SN.canonical_next frame base before oldEnvironment admissions)) :=
  ⟨SN.whole_first frame base before oldEnvironment admissions,
    SN.canonical_next frame base before oldEnvironment admissions⟩
end OriginalWord

end OriginalSourceConstantTransport

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
