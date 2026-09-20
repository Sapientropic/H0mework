import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated faithful realization of an additive state family

An actual source family `Generator → Carrier` first has its zero and addition
laws classified from the evaluator itself.  On the additive branch the
framework generates the `AddMonoidHom`, its kernel and cokernel residuals,
and classifies simultaneous faithfulness and coverage.  Only residual zero
generates a canonical additive equivalence.

The mouth is one shared occurrence of `(Root × evaluator)`.  It accepts no
additivity proof, homomorphism, injectivity, surjectivity, inverse, finite
enumeration, basis or determinant.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace AdditiveFamilyFaithfulRealization

noncomputable section

universe u v w

structure RootGeneratedAdditiveFamilyFaithfulRealizationAt
    {Root : Type w} {Generator : Type u} {Carrier : Type v}
    [AddCommGroup Generator] [AddCommGroup Carrier]
    (dependentOccurrence : RootedAccountedUnfolding
      (Root × (Generator → Carrier))) : Type (max u v w) where
  private mk ::

namespace RootGeneratedAdditiveFamilyFaithfulRealizationAt

variable {Root : Type w} {Generator : Type u} {Carrier : Type v}
variable [AddCommGroup Generator] [AddCommGroup Carrier]
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × (Generator → Carrier))}

def generate : RootGeneratedAdditiveFamilyFaithfulRealizationAt
    dependentOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : RootedAccountedUnfolding Root :=
  dependentOccurrence.map Prod.fst

def evaluatorOccurrence
    (_face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) :
    RootedAccountedUnfolding (Generator → Carrier) :=
  dependentOccurrence.map Prod.snd

def actualEvaluator
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Generator → Carrier :=
  face.evaluatorOccurrence.root

def AdditiveLaws
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Prop :=
  face.actualEvaluator 0 = 0 ∧
    ∀ left right, face.actualEvaluator (left + right) =
      face.actualEvaluator left + face.actualEvaluator right

structure GeneratedAdditiveCalculationAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Prop where
  private mk ::
  laws : face.AdditiveLaws

inductive AdditivityEquationObstructionAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Type (max u v) where
  | zero (fails : face.actualEvaluator 0 ≠ 0)
  | addition (left right : Generator)
      (fails : face.actualEvaluator (left + right) ≠
        face.actualEvaluator left + face.actualEvaluator right)

inductive AdditivitySettlementOutcome
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Type (max u v) where
  | additive (calculation : GeneratedAdditiveCalculationAt face)
  | obstructed (obstruction : AdditivityEquationObstructionAt face)

/-- Caller-free exact classification of the actual evaluator equations. -/
noncomputable def settleAdditivity
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : AdditivitySettlementOutcome face := by
  classical
  by_cases zeroLaw : face.actualEvaluator 0 = 0
  · by_cases addLaw : ∀ left right,
        face.actualEvaluator (left + right) =
          face.actualEvaluator left + face.actualEvaluator right
    · exact .additive ⟨zeroLaw, addLaw⟩
    · have existsLeft : ∃ left, ¬ ∀ right,
          face.actualEvaluator (left + right) =
            face.actualEvaluator left + face.actualEvaluator right := by
        simpa only [not_forall] using addLaw
      let left := Classical.choose existsLeft
      have leftFails : ¬ ∀ right,
          face.actualEvaluator (left + right) =
            face.actualEvaluator left + face.actualEvaluator right := by
        dsimp only [left]
        exact Classical.choose_spec existsLeft
      have existsRight : ∃ right,
          face.actualEvaluator (left + right) ≠
            face.actualEvaluator left + face.actualEvaluator right := by
        simpa only [not_forall] using leftFails
      let right := Classical.choose existsRight
      exact .obstructed
        (.addition left right (Classical.choose_spec existsRight))
  · exact .obstructed (.zero zeroLaw)

def additiveMap
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :
    Generator →+ Carrier where
  toFun := face.actualEvaluator
  map_zero' := calculation.laws.1
  map_add' := calculation.laws.2

def KernelResidual
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :
    AddSubgroup Generator :=
  (face.additiveMap calculation).ker

abbrev CokernelResidual
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :=
  Carrier ⧸ (face.additiveMap calculation).range

def FaithfulCoverageResidualVanishes
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop :=
  face.KernelResidual calculation = ⊥ ∧
    Subsingleton (face.CokernelResidual calculation)

structure GeneratedFaithfulCoverageResidualZeroAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop where
  private mk ::
  vanishes : face.FaithfulCoverageResidualVanishes calculation

structure FaithfulCoverageResidualObstructionAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop where
  private mk ::
  persists : ¬ face.FaithfulCoverageResidualVanishes calculation

inductive SettlementOutcome
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Type (max u v) where
  | additivityObstruction
      (obstruction : AdditivityEquationObstructionAt face)
  | residualObstruction
      (calculation : GeneratedAdditiveCalculationAt face)
      (obstruction : FaithfulCoverageResidualObstructionAt face calculation)
  | faithful
      (calculation : GeneratedAdditiveCalculationAt face)
      (residualZero : GeneratedFaithfulCoverageResidualZeroAt face calculation)

/-- Settlement after an actual relation calculation has ruled out the two
equation obstructions.  The generated additive token is still extracted from
`settle`; it is not constructed by the caller. -/
inductive PostAdditiveSettlementOutcome
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : Type (max u v) where
  | residual
      (calculation : GeneratedAdditiveCalculationAt face)
      (obstruction : FaithfulCoverageResidualObstructionAt face calculation)
  | faithful
      (calculation : GeneratedAdditiveCalculationAt face)
      (residualZero : GeneratedFaithfulCoverageResidualZeroAt face calculation)

/-- Total settlement.  A positive branch is generated only from the actual
evaluator equations and its actual kernel/cokernel. -/
noncomputable def settle
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) : SettlementOutcome face := by
  classical
  cases face.settleAdditivity with
  | obstructed obstruction => exact .additivityObstruction obstruction
  | additive calculation =>
      by_cases residualZero :
          face.FaithfulCoverageResidualVanishes calculation
      · exact .faithful calculation ⟨residualZero⟩
      · exact .residualObstruction calculation ⟨residualZero⟩

/-- Consume a proved relation calculation only to eliminate impossible
classifier branches.  Kernel and cokernel remain calculated by `settle`. -/
noncomputable def settleAfterAdditivity
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (actualRelations : face.AdditiveLaws) :
    PostAdditiveSettlementOutcome face := by
  cases face.settle with
  | additivityObstruction obstruction =>
      cases obstruction with
      | zero fails => exact False.elim (fails actualRelations.1)
      | addition left right fails =>
          exact False.elim (fails (actualRelations.2 left right))
  | residualObstruction calculation obstruction =>
      exact .residual calculation obstruction
  | faithful calculation residualZero =>
      exact .faithful calculation residualZero

/-- The additive token selected by the classifier after actual relations
have eliminated its obstruction branches. -/
theorem generatedAdditiveCalculation
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (actualRelations : face.AdditiveLaws) :
    GeneratedAdditiveCalculationAt face := by
  cases face.settleAfterAdditivity actualRelations with
  | residual calculation _ => exact calculation
  | faithful calculation _ => exact calculation

/-- Source-compatible component generated by the actual evaluator itself. -/
abbrev SourceComponent
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :=
  (face.additiveMap calculation).range

def sourceComponentMap
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :
    Generator →+ face.SourceComponent calculation :=
  (face.additiveMap calculation).rangeRestrict

theorem sourceComponentMap_surjective
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :
    Function.Surjective (face.sourceComponentMap calculation) := by
  rintro ⟨value, ⟨generator, generator_eq⟩⟩
  refine ⟨generator, Subtype.ext ?_⟩
  exact generator_eq

def SourceKernelResidualVanishes
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop :=
  (face.sourceComponentMap calculation).ker = ⊥

structure GeneratedSourceKernelResidualZeroAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop where
  private mk ::
  vanishes : face.SourceKernelResidualVanishes calculation

structure SourceKernelResidualObstructionAt
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Prop where
  private mk ::
  persists : ¬ face.SourceKernelResidualVanishes calculation

inductive SourceComponentSettlementOutcome
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) : Type (max u v) where
  | kernelObstruction
      (obstruction : SourceKernelResidualObstructionAt face calculation)
  | faithful
      (residualZero : GeneratedSourceKernelResidualZeroAt face calculation)

/-- The source component has coverage by construction; only its actual
kernel remains to classify. -/
noncomputable def settleSourceComponent
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face) :
    SourceComponentSettlementOutcome face calculation := by
  classical
  by_cases kernelZero : face.SourceKernelResidualVanishes calculation
  · exact .faithful ⟨kernelZero⟩
  · exact .kernelObstruction ⟨kernelZero⟩

theorem sourceComponentMap_injective
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face)
    (residualZero : GeneratedSourceKernelResidualZeroAt face calculation) :
    Function.Injective (face.sourceComponentMap calculation) :=
  (AddMonoidHom.ker_eq_bot_iff
    (face.sourceComponentMap calculation)).mp residualZero.vanishes

noncomputable def canonicalSourceComponentEquiv
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face)
    (residualZero : GeneratedSourceKernelResidualZeroAt face calculation) :
    Generator ≃+ face.SourceComponent calculation :=
  AddEquiv.ofBijective (face.sourceComponentMap calculation)
    ⟨face.sourceComponentMap_injective calculation residualZero,
      face.sourceComponentMap_surjective calculation⟩

theorem faithful_injective
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face)
    (residualZero : GeneratedFaithfulCoverageResidualZeroAt
      face calculation) :
    Function.Injective (face.additiveMap calculation) :=
  (AddMonoidHom.ker_eq_bot_iff (face.additiveMap calculation)).mp
    residualZero.vanishes.1

theorem faithful_surjective
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face)
    (residualZero : GeneratedFaithfulCoverageResidualZeroAt
      face calculation) :
    Function.Surjective (face.additiveMap calculation) := by
  apply AddMonoidHom.range_eq_top.mp
  exact QuotientAddGroup.subsingleton_iff.mp residualZero.vanishes.2

/-- Canonical additive equivalence generated only on the simultaneous
kernel/cokernel-zero branch. -/
noncomputable def canonicalEquiv
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence)
    (calculation : GeneratedAdditiveCalculationAt face)
    (residualZero : GeneratedFaithfulCoverageResidualZeroAt
      face calculation) : Generator ≃+ Carrier :=
  AddEquiv.ofBijective (face.additiveMap calculation)
    ⟨face.faithful_injective calculation residualZero,
      face.faithful_surjective calculation residualZero⟩

theorem preserves_shared_root_and_evaluator
    (face : RootGeneratedAdditiveFamilyFaithfulRealizationAt
      dependentOccurrence) :
    face.root = dependentOccurrence.map Prod.fst ∧
      face.evaluatorOccurrence = dependentOccurrence.map Prod.snd ∧
      face.actualEvaluator = dependentOccurrence.root.2 :=
  ⟨rfl, rfl, by
    simp [actualEvaluator, evaluatorOccurrence]⟩

end RootGeneratedAdditiveFamilyFaithfulRealizationAt

end

end AdditiveFamilyFaithfulRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
