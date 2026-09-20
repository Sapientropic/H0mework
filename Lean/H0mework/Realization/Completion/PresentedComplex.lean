import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import H0mework.Realization.Completion.FaithfulRealization
import H0mework.Foundation.Relations.AdditivePresentation
import H0mework.Realization.Completion.DerivedSettlement

/-!
# Root-generated cofinal presented complexes

A family of formal presentation histories becomes a cochain complex without
assuming that any degreewise completion is the actual carrier.  Generator
transport is forced by the differential of one actual rooted complex;
preservation of the observed generator and relation closures, relation
soundness, and the complex laws are all settled by the generic engine.

On the successful branch the engine generates both the completion complex
and its evaluation chain map to the actual complex.  It accepts no caller
differential, chain map, coverage witness, equivalence, finite model, or
perfectness receipt.  Derived equivalence is deliberately a later global
mapping-cofiber calculation, not a degreewise gate.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.defProp false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPresentedComplex

open CategoryTheory
open CofinalHistorySettlement
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open FiniteAdditiveRelationPresentation
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedAdicCofiber
open DerivedCofinalSettlement

noncomputable section

universe i w

attribute [local instance] HasDerivedCategory.standard

/-- Reinterpret an additive map using the particular `ℤ`-module structures
stored by `ModuleCat`.  This avoids the non-definitional instance diamond
between a bundled module and the canonical additive-group `ℤ` action. -/
private def intLinearMapOfAddMonoidHom
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {moduleM : Module ℤ M} {moduleN : Module ℤ N}
    (hom : M →+ N) : M →ₗ[ℤ] N where
  toFun := hom
  map_add' := hom.map_add
  map_smul' scalar value := by
    convert! hom.map_zsmul scalar value using 1
    · exact congr(hom $(int_smul_eq_zsmul ..))
    · exact int_smul_eq_zsmul ..

/-- Actual rooted cochain carrier together with one actual cofinal event
history in every degree.  Generator atoms are the actual degree elements;
the differential therefore generates their transport canonically. -/
structure RootGeneratedCofinalPresentedComplexDiagramAt
    {Index : Type i} (shape : ComplexShape Index)
    {Root : Type w} (rootOccurrence : RootedAccountedUnfolding Root)
    (actualComplexOccurrence : RootedAccountedUnfolding
      (HomologicalComplex (ModuleCat.{0} ℤ) shape)) : Type (max i w) where
  private mk ::
  seedOccurrence : ∀ degree, RootedAccountedUnfolding
    (PresentedRelationEventAt (actualComplexOccurrence.root.X degree))
  continuationOccurrence : ∀ degree, RootedAccountedUnfolding
    (PresentedRelationEventAt (actualComplexOccurrence.root.X degree) →
      RootedAccountedUnfolding
        (PresentedRelationEventAt (actualComplexOccurrence.root.X degree)))

namespace RootGeneratedCofinalPresentedComplexDiagramAt

variable {Index : Type i} {shape : ComplexShape Index}
variable {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (HomologicalComplex (ModuleCat.{0} ℤ) shape)}

def generate
    (seedOccurrence : ∀ degree, RootedAccountedUnfolding
      (PresentedRelationEventAt (actualComplexOccurrence.root.X degree)))
    (continuationOccurrence : ∀ degree, RootedAccountedUnfolding
      (PresentedRelationEventAt (actualComplexOccurrence.root.X degree) →
        RootedAccountedUnfolding
          (PresentedRelationEventAt
            (actualComplexOccurrence.root.X degree)))) :
    RootGeneratedCofinalPresentedComplexDiagramAt shape rootOccurrence
      actualComplexOccurrence :=
  ⟨seedOccurrence, continuationOccurrence⟩

def root
    (_diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :=
  rootOccurrence

def actualComplex
    (_diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :=
  actualComplexOccurrence.root

def history
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (degree : Index) : RootGeneratedCofinalHistoryAt rootOccurrence
      (diagram.seedOccurrence degree) (diagram.continuationOccurrence degree) :=
  RootGeneratedCofinalHistoryAt.generate

def identityEvaluatorOccurrence
    (_diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (degree : Index) : RootedAccountedUnfolding
      (actualComplexOccurrence.root.X degree →
        actualComplexOccurrence.root.X degree) :=
  RootedAccountedUnfolding.zero id

def degreeFace
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (degree : Index) : RootGeneratedCofinalFaithfulRealizationAt
      (diagram.history degree) (diagram.identityEvaluatorOccurrence degree) :=
  RootGeneratedCofinalFaithfulRealizationAt.generate

/-- Free generator transport is generated by the same actual
differential. -/
def freeDifferential
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (source target : Index) :
    (diagram.actualComplex.X source →₀ ℤ) →ₗ[ℤ]
      (diagram.actualComplex.X target →₀ ℤ) :=
  generatorMap
    (diagram.actualComplex.d source target).hom.toAddMonoidHom

def GeneratorClosurePreserved
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Prop :=
  ∀ source target value,
    value ∈ (diagram.history source).generatorClosure →
      diagram.freeDifferential source target value ∈
        (diagram.history target).generatorClosure

def RelationClosurePreserved
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Prop :=
  ∀ source target value,
    value ∈ (diagram.history source).relationClosure →
      diagram.freeDifferential source target value ∈
        (diagram.history target).relationClosure

structure GeneratedDifferentialClosureAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Type (max i w) where
  private mk ::
  generators : diagram.GeneratorClosurePreserved
  relations : diagram.RelationClosurePreserved

structure GeneratedDifferentialClosureObstructionAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Type (max i w) where
  private mk ::
  persists : ¬ (diagram.GeneratorClosurePreserved ∧
    diagram.RelationClosurePreserved)

abbrev DifferentialClosureOutcome
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :=
  Sum (GeneratedDifferentialClosureAt diagram)
    (GeneratedDifferentialClosureObstructionAt diagram)

/-- Caller-free settlement of both closure conditions. -/
noncomputable def settleDifferentialClosure
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :
    DifferentialClosureOutcome diagram := by
  classical
  by_cases closed : diagram.GeneratorClosurePreserved ∧
      diagram.RelationClosurePreserved
  · exact Sum.inl ⟨closed.1, closed.2⟩
  · exact Sum.inr ⟨closed⟩

def generatorClosureDifferential
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (source target : Index) :
    (diagram.history source).generatorClosure →ₗ[ℤ]
      (diagram.history target).generatorClosure :=
  LinearMap.codRestrict _
    ((diagram.freeDifferential source target).comp
      (diagram.history source).generatorClosure.subtype)
    (fun value => closure.generators source target value value.property)

theorem relationInGeneratorClosure_maps
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (source target : Index) :
    (diagram.history source).relationInGeneratorClosure ≤
      (diagram.history target).relationInGeneratorClosure.comap
        (diagram.generatorClosureDifferential closure source target) := by
  intro relation relation_mem
  exact closure.relations source target relation relation_mem

/-- Differential induced on the formal presented completions. -/
def completionDifferential
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (source target : Index) :
    (diagram.history source).CompletionCarrier →ₗ[ℤ]
      (diagram.history target).CompletionCarrier :=
  Submodule.mapQ
    (diagram.history source).relationInGeneratorClosure
    (diagram.history target).relationInGeneratorClosure
    (diagram.generatorClosureDifferential closure source target)
    (diagram.relationInGeneratorClosure_maps closure source target)

def CompletionLaws
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram) : Prop :=
  (∀ source target, ¬ shape.Rel source target →
      diagram.completionDifferential closure source target = 0) ∧
    (∀ source middle target,
      (diagram.completionDifferential closure middle target).comp
          (diagram.completionDifferential closure source middle) = 0)

structure GeneratedCompletionLawsAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram) : Type (max i w) where
  private mk ::
  laws : diagram.CompletionLaws closure

structure GeneratedCompletionLawObstructionAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram) : Type (max i w) where
  private mk ::
  persists : ¬ diagram.CompletionLaws closure

abbrev CompletionLawOutcome
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram) :=
  Sum (GeneratedCompletionLawsAt diagram closure)
    (GeneratedCompletionLawObstructionAt diagram closure)

/-- The quotient complex laws are calculated, never submitted. -/
noncomputable def settleCompletionLaws
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram) :
    CompletionLawOutcome diagram closure := by
  classical
  by_cases laws : diagram.CompletionLaws closure
  · exact Sum.inl ⟨laws⟩
  · exact Sum.inr ⟨laws⟩

def completionModule
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) (degree : Index) :
    ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ (diagram.history degree).CompletionCarrier

/-- One actual completion complex generated from the histories. -/
noncomputable def completionComplex
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure) :
    HomologicalComplex (ModuleCat.{0} ℤ) shape where
  X := diagram.completionModule
  d source target := ModuleCat.ofHom
    (diagram.completionDifferential closure source target)
  shape source target notRelated := by
    apply ModuleCat.hom_ext
    exact laws.laws.1 source target notRelated
  d_comp_d' source middle target sourceMiddle middleTarget := by
    apply ModuleCat.hom_ext
    exact laws.laws.2 source middle target

structure GeneratedDegreewiseRelationSoundnessAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Type (max i w) where
  private mk ::
  soundness : ∀ degree,
    GeneratedRelationSoundnessAt (diagram.degreeFace degree)

structure GeneratedDegreewiseRelationUnsoundObstructionAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) : Type (max i w) where
  private mk ::
  degree : Index
  notSound : ¬ (diagram.degreeFace degree).RelationsSound

abbrev RelationSoundnessOutcome
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :=
  Sum (GeneratedDegreewiseRelationSoundnessAt diagram)
    (GeneratedDegreewiseRelationUnsoundObstructionAt diagram)

private noncomputable def generatedSoundnessAt
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (degree : Index)
    (sound : (diagram.degreeFace degree).RelationsSound) :
    GeneratedRelationSoundnessAt (diagram.degreeFace degree) := by
  cases (diagram.degreeFace degree).settleRelations with
  | sound soundness => exact soundness
  | unsound obstruction => exact False.elim (obstruction.notSound sound)

/-- Relation soundness in every degree is calculated independently of
coverage. -/
noncomputable def settleRelationSoundness
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence) :
    RelationSoundnessOutcome diagram := by
  classical
  by_cases allSound : ∀ degree,
      (diagram.degreeFace degree).RelationsSound
  · exact Sum.inl
      ⟨fun degree => diagram.generatedSoundnessAt degree (allSound degree)⟩
  · have existsUnsound : ∃ degree,
        ¬ (diagram.degreeFace degree).RelationsSound := by
      simpa only [not_forall] using allSound
    exact Sum.inr
      ⟨Classical.choose existsUnsound,
        Classical.choose_spec existsUnsound⟩

def degreeEvaluation
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
    (degree : Index) :
    (diagram.history degree).CompletionCarrier →ₗ[ℤ]
      diagram.actualComplex.X degree :=
  intLinearMapOfAddMonoidHom
    ((diagram.degreeFace degree).completionEvaluation
      (soundness.soundness degree)).toAddMonoidHom

theorem degreeEvaluation_naturality
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
    (source target : Index) :
    (diagram.actualComplex.d source target).hom.comp
        (diagram.degreeEvaluation soundness source) =
      (diagram.degreeEvaluation soundness target).comp
        (diagram.completionDifferential closure source target) := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change diagram.actualComplex.d source target
      (FiniteAdditiveRelationPresentation.freeEvaluation
        (diagram.actualComplex.X source)
        representative.1) =
    FiniteAdditiveRelationPresentation.freeEvaluation
      (diagram.actualComplex.X target)
      (diagram.freeDifferential source target
        representative.1)
  exact DFunLike.congr_fun
    (freeEvaluation_naturality
      (diagram.actualComplex.d source target).hom.toAddMonoidHom).symm
    representative.1

/-- The completion-to-actual chain map is generated from the same actual
differential and the settled relation soundness. -/
noncomputable def evaluationMap
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    diagram.completionComplex closure laws ⟶ diagram.actualComplex where
  f degree := ModuleCat.ofHom (diagram.degreeEvaluation soundness degree)
  comm' source target _ := by
    apply ModuleCat.hom_ext
    change (diagram.actualComplex.d source target).hom.comp
        (diagram.degreeEvaluation soundness source) =
      (diagram.degreeEvaluation soundness target).comp
        (diagram.completionDifferential closure source target)
    exact diagram.degreeEvaluation_naturality closure soundness
      source target

def completionComplexOccurrence
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure) :
    RootedAccountedUnfolding
      (HomologicalComplex (ModuleCat.{0} ℤ) shape) :=
  RootedAccountedUnfolding.zero (diagram.completionComplex closure laws)

def evaluationMapOccurrence
    (diagram : RootGeneratedCofinalPresentedComplexDiagramAt shape
      rootOccurrence actualComplexOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    RootedAccountedUnfolding
      (diagram.completionComplex closure laws ⟶ diagram.actualComplex) :=
  RootedAccountedUnfolding.zero
    (diagram.evaluationMap closure laws soundness)

/-- Standard integral cochain specialization consumed by the derived
category kernel. -/
abbrev RootGeneratedIntegralCofinalPresentedComplexDiagramAt
    {Root : Type w} (rootOccurrence : RootedAccountedUnfolding Root)
    (actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)) :=
  RootGeneratedCofinalPresentedComplexDiagramAt (ComplexShape.up ℤ)
    rootOccurrence actualCochainOccurrence

def derivedFace
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    RootGeneratedDerivedAdicCofiberAt diagram.root
      (diagram.completionComplexOccurrence closure laws)
      actualCochainOccurrence
      (diagram.evaluationMapOccurrence closure laws soundness) :=
  RootGeneratedDerivedAdicCofiberAt.generate

def DerivedResidualVanishes
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) : Prop :=
  IsZero (diagram.derivedFace closure laws soundness).derivedTriangle.obj₁

structure GeneratedDerivedResidualZeroAt
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    Type w where
  private mk ::
  vanishes : diagram.DerivedResidualVanishes closure laws soundness

structure GeneratedDerivedResidualObstructionAt
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    Type w where
  private mk ::
  persists : ¬ diagram.DerivedResidualVanishes closure laws soundness

abbrev DerivedResidualOutcome
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :=
  Sum (GeneratedDerivedResidualZeroAt diagram closure laws soundness)
    (GeneratedDerivedResidualObstructionAt diagram closure laws soundness)

/-- Global mapping-cofiber settlement.  There is no degreewise coverage
condition in this decision. -/
noncomputable def settleDerivedResidual
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram) :
    DerivedResidualOutcome diagram closure laws soundness := by
  classical
  by_cases residualZero :
      diagram.DerivedResidualVanishes closure laws soundness
  · exact Sum.inl ⟨residualZero⟩
  · exact Sum.inr ⟨residualZero⟩

theorem derivedEvaluationIsIso
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
    (residualZero : GeneratedDerivedResidualZeroAt
      diagram closure laws soundness) :
    IsIso (DerivedCategory.Q.map
      (diagram.evaluationMap closure laws soundness)) := by
  exact ((diagram.derivedFace closure laws soundness).derivedTriangle
    |>.isZero₁_iff_isIso₂
      (diagram.derivedFace closure laws soundness
        |>.derivedTriangle_distinguished)).mp residualZero.vanishes

/-- The zero-residual branch installs the already stable generic global
settlement mouth. -/
noncomputable def globalSettlement
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence)
    (closure : GeneratedDifferentialClosureAt diagram)
    (laws : GeneratedCompletionLawsAt diagram closure)
    (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
    (residualZero : GeneratedDerivedResidualZeroAt
      diagram closure laws soundness) :
    RootGeneratedDerivedCofinalSettlementAt diagram.root
      (diagram.completionComplexOccurrence closure laws)
      actualCochainOccurrence
      (diagram.evaluationMapOccurrence closure laws soundness) := by
  let derivedIso : IsIso (DerivedCategory.Q.map
      (diagram.evaluationMapOccurrence closure laws soundness).root) := by
    change IsIso (DerivedCategory.Q.map
      (diagram.evaluationMap closure laws soundness))
    exact diagram.derivedEvaluationIsIso closure laws soundness residualZero
  exact @RootGeneratedDerivedCofinalSettlementAt.generate
    Root ℤ inferInstance diagram.root
    (diagram.completionComplexOccurrence closure laws)
    actualCochainOccurrence
    (diagram.evaluationMapOccurrence closure laws soundness)
    derivedIso

/-- Exact total outcome of the rooted history calculation. -/
inductive SettlementOutcome
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence) : Type w where
  | differentialObstruction
      (obstruction : GeneratedDifferentialClosureObstructionAt diagram)
  | lawObstruction
      (closure : GeneratedDifferentialClosureAt diagram)
      (obstruction : GeneratedCompletionLawObstructionAt diagram closure)
  | relationObstruction
      (obstruction : GeneratedDegreewiseRelationUnsoundObstructionAt diagram)
  | residualObstruction
      (closure : GeneratedDifferentialClosureAt diagram)
      (laws : GeneratedCompletionLawsAt diagram closure)
      (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
      (obstruction : GeneratedDerivedResidualObstructionAt
        diagram closure laws soundness)
  | settled
      (closure : GeneratedDifferentialClosureAt diagram)
      (laws : GeneratedCompletionLawsAt diagram closure)
      (soundness : GeneratedDegreewiseRelationSoundnessAt diagram)
      (residualZero : GeneratedDerivedResidualZeroAt
        diagram closure laws soundness)

/-- Stable caller-free mouth from rooted histories through the generated
completion chain map to the global derived residual. -/
noncomputable def settle
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    {actualCochainOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex ℤ)}
    (diagram : RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      rootOccurrence actualCochainOccurrence) :
    SettlementOutcome diagram := by
  classical
  match diagram.settleDifferentialClosure with
  | Sum.inr obstruction => exact .differentialObstruction obstruction
  | Sum.inl closure =>
      match diagram.settleCompletionLaws closure with
      | Sum.inr obstruction => exact .lawObstruction closure obstruction
      | Sum.inl laws =>
          match diagram.settleRelationSoundness with
          | Sum.inr obstruction => exact .relationObstruction obstruction
          | Sum.inl soundness =>
              match diagram.settleDerivedResidual closure laws soundness with
              | Sum.inr obstruction =>
                  exact .residualObstruction closure laws soundness obstruction
              | Sum.inl residualZero =>
                  exact .settled closure laws soundness residualZero

end RootGeneratedCofinalPresentedComplexDiagramAt

end

end CofinalPresentedComplex
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
