import H0mework.Foundation.Cofinal.KernelCompletion

/-!
# Relative-source evaluator normalization

An evaluator tower may commute only after an actual source automorphism at
each successor.  Accumulating the inverse source automorphisms normalizes that
tower to the existing fixed-source `AdditiveCofinalEvaluatorData` interface.
The induced quotient tower is canonically conjugate to the original relative
quotient tower.  No scalar inverse, localization, finiteness, or determinant
input is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedRelativeSourceEvaluatorNormalization

open CofinalKernelCompletion

noncomputable section

universe u

variable {Generator : Type u} [AddCommGroup Generator]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)]

/-- Evaluator data whose successor square also moves the source by an
additive automorphism. -/
structure RelativeData
    (Generator : Type u) [AddCommGroup Generator]
    (Carrier : Nat → Type u) [∀ stage, AddCommGroup (Carrier stage)] where
  evaluator : (stage : Nat) → Generator →+ Carrier stage
  sourceTransition : (stage : Nat) → Generator ≃+ Generator
  targetTransition : (stage : Nat) → Carrier (stage + 1) →+ Carrier stage

namespace RelativeData

/-- The actual relative successor square. -/
def Compatible (data : RelativeData Generator Carrier) : Prop :=
  ∀ stage,
    (data.targetTransition stage).comp (data.evaluator (stage + 1)) =
      (data.evaluator stage).comp
        (data.sourceTransition stage).toAddMonoidHom

/-- Cumulative inverse source correction.  With Lean's `trans` convention,
`C_(n+1) = S_n⁻¹ ∘ C_n`. -/
def cumulativeInverse (data : RelativeData Generator Carrier) :
    Nat → Generator ≃+ Generator
  | 0 => AddEquiv.refl Generator
  | stage + 1 =>
      (data.cumulativeInverse stage).trans
        (data.sourceTransition stage).symm

/-- The cumulative correction cancels the next source transition exactly. -/
@[simp] theorem sourceTransition_cumulativeInverse
    (data : RelativeData Generator Carrier) (stage : Nat) :
    (data.sourceTransition stage).toAddMonoidHom.comp
        (data.cumulativeInverse (stage + 1)).toAddMonoidHom =
      (data.cumulativeInverse stage).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro value
  simp [RelativeData.cumulativeInverse]

/-- Fixed-source evaluator obtained by the cumulative inverse correction. -/
def normalizedEvaluator
    (data : RelativeData Generator Carrier) (stage : Nat) :
    Generator →+ Carrier stage :=
  (data.evaluator stage).comp
    (data.cumulativeInverse stage).toAddMonoidHom

/-- The relative tower as an ordinary additive cofinal evaluator tower. -/
def normalizedData (data : RelativeData Generator Carrier) :
    AdditiveCofinalEvaluatorData Generator Carrier where
  evaluator := data.normalizedEvaluator
  transition := data.targetTransition

/-- Relative compatibility becomes strict fixed-source compatibility. -/
theorem normalizedData_strictCompatible
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) :
    ∀ stage,
      ((data.normalizedData).transition stage).comp
          ((data.normalizedData).evaluator (stage + 1)) =
        (data.normalizedData).evaluator stage := by
  intro stage
  apply AddMonoidHom.ext
  intro value
  change data.targetTransition stage
      (data.evaluator (stage + 1)
        (data.cumulativeInverse (stage + 1) value)) =
    data.evaluator stage (data.cumulativeInverse stage value)
  have square := DFunLike.congr_fun (compatible stage)
    (data.cumulativeInverse (stage + 1) value)
  change data.targetTransition stage
      (data.evaluator (stage + 1)
        (data.cumulativeInverse (stage + 1) value)) =
    data.evaluator stage
      (data.sourceTransition stage
        (data.cumulativeInverse (stage + 1) value)) at square
  rw [square]
  congr 1
  exact DFunLike.congr_fun
    (data.sourceTransition_cumulativeInverse stage) value

/-- Kernel membership after normalization is exactly membership of the
cumulative correction in the original evaluator kernel. -/
theorem normalizedKernel_mem_iff
    (data : RelativeData Generator Carrier)
    (stage : Nat) (value : Generator) :
    value ∈ ((data.normalizedData).evaluator stage).ker ↔
      data.cumulativeInverse stage value ∈ (data.evaluator stage).ker := by
  rfl

def stageKernel
    (data : RelativeData Generator Carrier) (stage : Nat) :
    AddSubgroup Generator :=
  (data.evaluator stage).ker

abbrev StageQuotient
    (data : RelativeData Generator Carrier) (stage : Nat) :=
  Generator ⧸ data.stageKernel stage

/-- A relative successor square sends the high-stage kernel into the
low-stage kernel by the actual source automorphism. -/
theorem sourceTransition_maps_stageKernel
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) :
    data.stageKernel (stage + 1) ≤
      (data.stageKernel stage).comap
        (data.sourceTransition stage).toAddMonoidHom := by
  intro value highKernel
  change value ∈ (data.evaluator (stage + 1)).ker at highKernel
  change data.sourceTransition stage value ∈
    (data.evaluator stage).ker
  rw [AddMonoidHom.mem_ker] at highKernel ⊢
  have square := DFunLike.congr_fun (compatible stage) value
  change data.targetTransition stage
      (data.evaluator (stage + 1) value) =
    data.evaluator stage (data.sourceTransition stage value) at square
  rw [highKernel, map_zero] at square
  exact square.symm

/-- Original quotient successor, induced by the actual source
automorphism rather than the identity. -/
def quotientTransition
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) :
    data.StageQuotient (stage + 1) →+ data.StageQuotient stage :=
  QuotientAddGroup.map (data.stageKernel (stage + 1))
    (data.stageKernel stage)
    (data.sourceTransition stage).toAddMonoidHom
    (data.sourceTransition_maps_stageKernel compatible stage)

@[simp] theorem quotientTransition_mk
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) (value : Generator) :
    data.quotientTransition compatible stage
        (QuotientAddGroup.mk' (data.stageKernel (stage + 1)) value) =
      QuotientAddGroup.mk' (data.stageKernel stage)
        (data.sourceTransition stage value) := by
  rfl

def normalizedStageKernel
    (data : RelativeData Generator Carrier) (stage : Nat) :
    AddSubgroup Generator :=
  ((data.normalizedData).evaluator stage).ker

abbrev NormalizedStageQuotient
    (data : RelativeData Generator Carrier) (stage : Nat) :=
  Generator ⧸ data.normalizedStageKernel stage

theorem normalizedStageKernel_succ_le
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) :
    data.normalizedStageKernel (stage + 1) ≤
      data.normalizedStageKernel stage := by
  intro value highKernel
  change value ∈
    ((data.normalizedData).evaluator (stage + 1)).ker at highKernel
  change value ∈ ((data.normalizedData).evaluator stage).ker
  rw [AddMonoidHom.mem_ker] at highKernel ⊢
  have square := DFunLike.congr_fun
    (data.normalizedData_strictCompatible compatible stage) value
  change data.targetTransition stage
      ((data.normalizedData).evaluator (stage + 1) value) =
    (data.normalizedData).evaluator stage value at square
  rw [highKernel, map_zero] at square
  exact square.symm

/-- The normalized quotient successor is the standard identity-induced
transition used by the existing cofinal evaluator kernel. -/
def normalizedQuotientTransition
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) :
    data.NormalizedStageQuotient (stage + 1) →+
      data.NormalizedStageQuotient stage :=
  QuotientAddGroup.map (data.normalizedStageKernel (stage + 1))
    (data.normalizedStageKernel stage) (AddMonoidHom.id Generator)
    (data.normalizedStageKernel_succ_le compatible stage)

/-- Cumulative correction descends from the normalized quotient to the
original relative quotient. -/
def normalizedToRelative
    (data : RelativeData Generator Carrier) (stage : Nat) :
    data.NormalizedStageQuotient stage →+ data.StageQuotient stage :=
  QuotientAddGroup.map (data.normalizedStageKernel stage)
    (data.stageKernel stage)
    (data.cumulativeInverse stage).toAddMonoidHom (by
      intro value membership
      change value ∈ ((data.normalizedData).evaluator stage).ker at membership
      change data.cumulativeInverse stage value ∈
        (data.evaluator stage).ker
      rw [AddMonoidHom.mem_ker] at membership ⊢
      exact membership)

/-- The inverse cumulative correction descends in the opposite direction. -/
def relativeToNormalized
    (data : RelativeData Generator Carrier) (stage : Nat) :
    data.StageQuotient stage →+ data.NormalizedStageQuotient stage :=
  QuotientAddGroup.map (data.stageKernel stage)
    (data.normalizedStageKernel stage)
    (data.cumulativeInverse stage).symm.toAddMonoidHom (by
      intro value membership
      change value ∈ (data.evaluator stage).ker at membership
      change (data.cumulativeInverse stage).symm value ∈
        ((data.normalizedData).evaluator stage).ker
      rw [AddMonoidHom.mem_ker] at membership ⊢
      change data.evaluator stage
        (data.cumulativeInverse stage
          ((data.cumulativeInverse stage).symm value)) = 0
      simpa using membership)

/-- Each normalized quotient is canonically the original relative quotient. -/
def normalizedRelativeQuotientEquiv
    (data : RelativeData Generator Carrier) (stage : Nat) :
    data.NormalizedStageQuotient stage ≃+ data.StageQuotient stage where
  toFun := data.normalizedToRelative stage
  invFun := data.relativeToNormalized stage
  left_inv := by
    intro quotient
    induction quotient using QuotientAddGroup.induction_on with
    | H value =>
        change QuotientAddGroup.mk' (data.normalizedStageKernel stage)
            ((data.cumulativeInverse stage).symm
              (data.cumulativeInverse stage value)) =
          QuotientAddGroup.mk' (data.normalizedStageKernel stage) value
        simp
  right_inv := by
    intro quotient
    induction quotient using QuotientAddGroup.induction_on with
    | H value =>
        change QuotientAddGroup.mk' (data.stageKernel stage)
            (data.cumulativeInverse stage
              ((data.cumulativeInverse stage).symm value)) =
          QuotientAddGroup.mk' (data.stageKernel stage) value
        simp
  map_add' := map_add (data.normalizedToRelative stage)

/-- The normalized and relative quotient transitions are conjugate through
the cumulative source correction. -/
theorem quotientTransition_conjugacy
    (data : RelativeData Generator Carrier)
    (compatible : data.Compatible) (stage : Nat) :
    (data.normalizedRelativeQuotientEquiv stage).toAddMonoidHom.comp
        (data.normalizedQuotientTransition compatible stage) =
      (data.quotientTransition compatible stage).comp
        (data.normalizedRelativeQuotientEquiv (stage + 1)).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H value =>
      change QuotientAddGroup.mk' (data.stageKernel stage)
          (data.cumulativeInverse stage value) =
        QuotientAddGroup.mk' (data.stageKernel stage)
          (data.sourceTransition stage
            (data.cumulativeInverse (stage + 1) value))
      have correction := DFunLike.congr_fun
        (data.sourceTransition_cumulativeInverse stage) value
      change data.sourceTransition stage
          (data.cumulativeInverse (stage + 1) value) =
        data.cumulativeInverse stage value at correction
      rw [correction]

end RelativeData

end
end SourceGeneratedRelativeSourceEvaluatorNormalization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
