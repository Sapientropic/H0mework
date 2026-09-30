import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.GroupTheory.QuotientGroup.Basic
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated cofinal completion by evaluator kernels

An actual compatible family of additive evaluators canonically generates
the inverse tower of source quotients by their kernels, its categorical
limit, and the universal source-to-completion map.  The caller supplies no
quotient tower, completion carrier, cone, limit or injectivity certificate.

Compatibility and separation remain explicit calculation receipts over the
actual evaluator history.  They are not fields of the source occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalKernelCompletion

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u w

structure AdditiveCofinalEvaluatorData
    (Generator : Type u) [AddCommGroup Generator]
    (Carrier : Nat → Type u) [∀ stage, AddCommGroup (Carrier stage)] where
  evaluator : (stage : Nat) → Generator →+ Carrier stage
  transition : (stage : Nat) → Carrier (stage + 1) →+ Carrier stage

structure RootGeneratedCofinalKernelCompletionAt
    {Root : Type w} {Generator : Type u} [AddCommGroup Generator]
    {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
    (dependentOccurrence : RootedAccountedUnfolding
      (Root × AdditiveCofinalEvaluatorData Generator Carrier)) :
    Type (max u w) where
  private mk ::

namespace RootGeneratedCofinalKernelCompletionAt

variable {Root : Type w} {Generator : Type u} [AddCommGroup Generator]
variable {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × AdditiveCofinalEvaluatorData Generator Carrier)}

def generate : RootGeneratedCofinalKernelCompletionAt dependentOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    RootedAccountedUnfolding Root :=
  dependentOccurrence.map Prod.fst

def dataOccurrence
    (_face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    RootedAccountedUnfolding
      (AdditiveCofinalEvaluatorData Generator Carrier) :=
  dependentOccurrence.map Prod.snd

def data
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    AdditiveCofinalEvaluatorData Generator Carrier :=
  face.dataOccurrence.root

def evaluator
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) : Generator →+ Carrier stage :=
  face.data.evaluator stage

def transition
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) : Carrier (stage + 1) →+ Carrier stage :=
  face.data.transition stage

def CompatibilityLaws
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) : Prop :=
  ∀ stage, (face.transition stage).comp (face.evaluator (stage + 1)) =
    face.evaluator stage

structure GeneratedCompatibilityCalculationAt
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) : Prop where
  private mk ::
  laws : face.CompatibilityLaws

theorem generateCompatibility
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (laws : face.CompatibilityLaws) :
    GeneratedCompatibilityCalculationAt face :=
  ⟨laws⟩

def stageKernel
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) : AddSubgroup Generator :=
  (face.evaluator stage).ker

abbrev StageQuotient
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) :=
  Generator ⧸ face.stageKernel stage

theorem stageKernel_succ_le
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.stageKernel (stage + 1) ≤ face.stageKernel stage := by
  intro generator highKernel
  change generator ∈ (face.evaluator (stage + 1)).ker at highKernel
  change generator ∈ (face.evaluator stage).ker
  rw [AddMonoidHom.mem_ker] at highKernel ⊢
  have compatible := DFunLike.congr_fun (calculation.laws stage) generator
  change face.transition stage (face.evaluator (stage + 1) generator) =
    face.evaluator stage generator at compatible
  rw [highKernel, map_zero] at compatible
  exact compatible.symm

/-- Canonical successor quotient map induced by the identity on the source
generator. -/
def quotientTransition
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.StageQuotient (stage + 1) →+ face.StageQuotient stage :=
  QuotientAddGroup.map (face.stageKernel (stage + 1))
    (face.stageKernel stage) (AddMonoidHom.id Generator) (by
      simpa using face.stageKernel_succ_le calculation stage)

@[reducible] noncomputable def quotientTower
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    ℕᵒᵖ ⥤ AddCommGrpCat :=
  Functor.ofOpSequence
    (X := fun stage ↦ AddCommGrpCat.of (face.StageQuotient stage))
    (fun stage ↦ AddCommGrpCat.ofHom
      (face.quotientTransition calculation stage))

@[reducible] noncomputable def carrierTower
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    ℕᵒᵖ ⥤ AddCommGrpCat :=
  Functor.ofOpSequence
    (X := fun stage ↦ AddCommGrpCat.of (Carrier stage))
    (fun stage ↦ AddCommGrpCat.ofHom (face.transition stage))

def stageRealization
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) :
    face.StageQuotient stage →+ Carrier stage :=
  QuotientAddGroup.kerLift (face.evaluator stage)

theorem stageRealization_injective
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) :
    Function.Injective (face.stageRealization stage) :=
  QuotientAddGroup.kerLift_injective (face.evaluator stage)

noncomputable def realizationNatTrans
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    face.quotientTower calculation ⟶ face.carrierTower :=
  NatTrans.ofOpSequence
    (fun stage ↦ AddCommGrpCat.ofHom (face.stageRealization stage))
    (fun stage ↦ by
      simp only [quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply AddCommGrpCat.ext
      intro quotient
      induction quotient using QuotientAddGroup.induction_on with
      | H generator =>
          change face.evaluator stage generator =
            face.transition stage (face.evaluator (stage + 1) generator)
          exact (DFunLike.congr_fun (calculation.laws stage) generator).symm)

def quotientMap
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) : Generator →+ face.StageQuotient stage :=
  QuotientAddGroup.mk' (face.stageKernel stage)

noncomputable def sourceState
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    (Functor.const ℕᵒᵖ).obj (AddCommGrpCat.of Generator) ⟶
      face.quotientTower calculation :=
  NatTrans.ofOpSequence
    (fun stage ↦ AddCommGrpCat.ofHom (face.quotientMap stage))
    (fun stage ↦ by
      simp only [Functor.const_obj_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply AddCommGrpCat.ext
      intro generator
      change face.quotientMap stage generator =
        face.quotientTransition calculation stage
          (face.quotientMap (stage + 1) generator)
      rfl)

noncomputable def sourceCone
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    Cone (face.quotientTower calculation) :=
  Cone.mk (AddCommGrpCat.of Generator) (face.sourceState calculation)

noncomputable def completion
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    AddCommGrpCat :=
  limit (face.quotientTower calculation)

noncomputable def carrierLimit
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    AddCommGrpCat :=
  limit face.carrierTower

/-- The completed source quotient tower maps canonically into the completed
actual carrier tower. -/
noncomputable def completionRealization
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    face.completion calculation ⟶ face.carrierLimit :=
  limMap (face.realizationNatTrans calculation)

noncomputable def carrierRestriction
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (stage : Nat) :
    face.carrierLimit ⟶ AddCommGrpCat.of (Carrier stage) :=
  limit.π face.carrierTower (Opposite.op stage)

set_option linter.style.haveILetI false in
theorem completionRealization_injective
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    Function.Injective (face.completionRealization calculation) := by
  letI : ∀ index, Mono ((face.realizationNatTrans calculation).app index) := by
    intro index
    rcases index with ⟨stage⟩
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    exact face.stageRealization_injective stage
  change Function.Injective (limMap (face.realizationNatTrans calculation))
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- The only residual left after stagewise kernel completion: compatible
completed carrier states not covered by the completed source. -/
abbrev CompletionResidual
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :=
  face.carrierLimit ⧸
    (face.completionRealization calculation).hom.range

def CoverageResidualVanishes
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) : Prop :=
  Subsingleton (face.CompletionResidual calculation)

structure GeneratedCoverageResidualZeroAt
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) : Prop where
  private mk ::
  vanishes : face.CoverageResidualVanishes calculation

theorem generateCoverageResidualZero
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (vanishes : face.CoverageResidualVanishes calculation) :
    GeneratedCoverageResidualZeroAt face calculation :=
  ⟨vanishes⟩

structure CoverageResidualObstructionAt
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) : Prop where
  private mk ::
  persists : ¬ face.CoverageResidualVanishes calculation

inductive CoverageSettlementOutcome
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) : Type (max u w) where
  | covered (residualZero : GeneratedCoverageResidualZeroAt face calculation)
  | obstructed (obstruction : CoverageResidualObstructionAt face calculation)

/-- Honest total classifier of the actual completed residual.  Its totality
is not a positive coverage theorem. -/
noncomputable def settleCoverage
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    CoverageSettlementOutcome face calculation := by
  classical
  by_cases vanishes : face.CoverageResidualVanishes calculation
  · exact .covered ⟨vanishes⟩
  · exact .obstructed ⟨vanishes⟩

theorem completionRealization_surjective
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (residualZero : GeneratedCoverageResidualZeroAt face calculation) :
    Function.Surjective (face.completionRealization calculation) := by
  apply AddMonoidHom.range_eq_top.mp
  exact QuotientAddGroup.subsingleton_iff.mp residualZero.vanishes

/-- Canonical equivalence generated only on the actual zero-coverage branch. -/
noncomputable def canonicalCompletionEquiv
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (residualZero : GeneratedCoverageResidualZeroAt face calculation) :
    face.completion calculation ≃+
      face.carrierLimit :=
  AddEquiv.ofBijective (face.completionRealization calculation).hom
    ⟨face.completionRealization_injective calculation,
      face.completionRealization_surjective calculation residualZero⟩

noncomputable def completionMap
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    AddCommGrpCat.of Generator ⟶ face.completion calculation :=
  limit.lift (face.quotientTower calculation) (face.sourceCone calculation)

noncomputable def restriction
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.completion calculation ⟶
      AddCommGrpCat.of (face.StageQuotient stage) :=
  limit.π (face.quotientTower calculation) (Opposite.op stage)

@[reassoc (attr := simp)] theorem completionMap_restriction
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.completionMap calculation ≫ face.restriction calculation stage =
      AddCommGrpCat.ofHom (face.quotientMap stage) :=
  limit.lift_π (face.sourceCone calculation) (Opposite.op stage)

@[reassoc (attr := simp)] theorem completionRealization_carrierRestriction
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.completionRealization calculation ≫ face.carrierRestriction stage =
      face.restriction calculation stage ≫
        AddCommGrpCat.ofHom (face.stageRealization stage) := by
  change
    (limit.isLimit face.carrierTower).map
          (limit.cone (face.quotientTower calculation))
          (face.realizationNatTrans calculation) ≫
        (limit.cone face.carrierTower).π.app (Opposite.op stage) =
      (limit.cone (face.quotientTower calculation)).π.app
          (Opposite.op stage) ≫
        (face.realizationNatTrans calculation).app (Opposite.op stage)
  exact IsLimit.map_π _ _ _ _

@[reassoc (attr := simp)] theorem source_to_carrier_restriction
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    face.completionMap calculation ≫
        face.completionRealization calculation ≫
        face.carrierRestriction stage =
      AddCommGrpCat.ofHom (face.evaluator stage) := by
  rw [face.completionRealization_carrierRestriction,
    ← Category.assoc, face.completionMap_restriction]
  apply AddCommGrpCat.ext
  intro generator
  rfl

def KernelSeparated
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) : Prop :=
  ∀ generator, (∀ stage, face.evaluator stage generator = 0) →
    generator = 0

structure GeneratedKernelSeparationAt
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) : Prop where
  private mk ::
  separates : face.KernelSeparated

theorem generateKernelSeparation
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (separates : face.KernelSeparated) :
    GeneratedKernelSeparationAt face :=
  ⟨separates⟩

theorem evaluator_eq_zero_of_completionMap_eq_zero
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (generator : Generator)
    (completionZero : face.completionMap calculation generator = 0)
    (stage : Nat) :
    face.evaluator stage generator = 0 := by
  have atStage := congrArg
    (fun value ↦ (face.restriction calculation stage).hom value)
    completionZero
  simp only [map_zero] at atStage
  have projection := ConcreteCategory.congr_hom
    (face.completionMap_restriction calculation stage) generator
  have quotientZero : face.quotientMap stage generator = 0 := by
    have generated := projection.symm.trans atStage
    change face.quotientMap stage generator = 0 at generated
    exact generated
  change (generator : face.StageQuotient stage) = 0 at quotientZero
  have kernelMembership : generator ∈ face.stageKernel stage :=
    (QuotientAddGroup.eq_zero_iff generator).mp quotientZero
  exact AddMonoidHom.mem_ker.mp kernelMembership

theorem completionMap_injective
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (separation : GeneratedKernelSeparationAt face) :
    Function.Injective (face.completionMap calculation) := by
  apply (injective_iff_map_eq_zero
    (face.completionMap calculation).hom).mpr
  intro generator completionZero
  apply separation.separates generator
  intro stage
  exact face.evaluator_eq_zero_of_completionMap_eq_zero calculation
    generator completionZero stage

theorem preserves_root_and_actual_data
    (face : RootGeneratedCofinalKernelCompletionAt dependentOccurrence) :
    face.root = dependentOccurrence.map Prod.fst ∧
      face.dataOccurrence = dependentOccurrence.map Prod.snd ∧
      face.data = dependentOccurrence.root.2 :=
  ⟨rfl, rfl, by simp [data, dataOccurrence]⟩

end RootGeneratedCofinalKernelCompletionAt
end
end CofinalKernelCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
