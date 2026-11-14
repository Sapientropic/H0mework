import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarCoimage

/-! Scalar extension of the relation differential of the same actual receipt.
The coefficients extend its already installed integer boundaries; no new
relation, source event, or quotient-soundness witness is supplied. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalRelationGeneratedComplex
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section
variable {D : Dynamics.{0}} {Carrier : Type} [CommRing Carrier]

/-- The actual integer relation differential, extended along the original
value ring. Its input indexes precisely the old history's relation closure. -/
def valueRelationAction (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (((historyLaw law).historyAt occurrence).relationClosure →₀ Carrier) →ₗ[Carrier]
      ValueWords law :=
  Finsupp.linearCombination Carrier fun relation =>
    integerToValueWords law (installedRelationAction law occurrence relation).1

theorem valueRelationAction_single (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (relation : ((historyLaw law).historyAt occurrence).relationClosure)
    (coefficient : Carrier) :
    valueRelationAction law occurrence (Finsupp.single relation coefficient) =
      coefficient • integerToValueWords law
        (installedRelationAction law occurrence relation).1 := by
  simp [valueRelationAction]

abbrev valueRelationCompletion (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :=
  ValueWords law ⧸ LinearMap.range (valueRelationAction law occurrence)

def valueRelationProjection (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ValueWords law →ₗ[Carrier] valueRelationCompletion law occurrence :=
  (LinearMap.range (valueRelationAction law occurrence)).mkQ

theorem valueRelationProjection_zero_iff (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : ValueWords law) :
    valueRelationProjection law occurrence word = 0 ↔
      ∃ relations, valueRelationAction law occurrence relations = word := by
  rw [← LinearMap.mem_range]
  exact Submodule.Quotient.mk_eq_zero _

theorem valueRelationProjection_old_boundary (law : Law D Carrier)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (relation : ((historyLaw law).historyAt occurrence).relationClosure) :
    valueRelationProjection law occurrence
      (integerToValueWords law
        (installedRelationAction law occurrence relation).1) = 0 := by
  apply (valueRelationProjection_zero_iff law occurrence _).2
  refine ⟨Finsupp.single relation 1, ?_⟩
  simpa using valueRelationAction_single law occurrence relation 1

/-- The old integral closure enters this same relation quotient. This is a
source square, not an assertion that scalar extension reflects nonzero words. -/
def oldClosureValueProjection (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ((historyLaw law).historyAt occurrence).generatorClosure →ₗ[ℤ]
      valueRelationCompletion law occurrence :=
  ((valueRelationProjection law occurrence).restrictScalars ℤ).comp
    ((integerToValueWords law).comp
      ((historyLaw law).historyAt occurrence).generatorClosure.subtype)

theorem oldClosureValueProjection_kills_original_relation
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ((historyLaw law).historyAt occurrence).relationInGeneratorClosure ≤
      LinearMap.ker (oldClosureValueProjection law occurrence) := by
  intro word belongs
  let history := (historyLaw law).historyAt occurrence
  let oldRelation : history.relationClosure := ⟨word.1, belongs⟩
  have same : installedRelationAction law occurrence oldRelation = word := by
    apply Subtype.ext
    simp [installedRelationAction, cochainComponent, relationInclusion,
      oldRelation]
  change valueRelationProjection law occurrence
    (integerToValueWords law word.1) = 0
  rw [← same]
  exact valueRelationProjection_old_boundary law occurrence oldRelation

def oldCompletionToValueRelation (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ((historyLaw law).historyAt occurrence).CompletionCarrier →ₗ[ℤ]
      valueRelationCompletion law occurrence :=
  Submodule.liftQ _ (oldClosureValueProjection law occurrence)
    (oldClosureValueProjection_kills_original_relation law occurrence)

theorem oldCompletion_value_relation_square (law : Law D Carrier)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (oldCompletionToValueRelation law occurrence).comp
        ((historyLaw law).historyAt occurrence).completionProjection =
      oldClosureValueProjection law occurrence := by
  apply LinearMap.ext
  intro word
  rfl

/-- A full Carrier-linear readout descends exactly when it kills each actual
old relation boundary; linearity then kills their entire Carrier-span. -/
theorem valueRelation_descend_iff (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    {Target : Type} [AddCommGroup Target] [Module Carrier Target]
    (read : ValueWords law →ₗ[Carrier] Target) :
    (∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier] Target,
      factor.comp (valueRelationProjection law occurrence) = read) ↔
    ∀ relation : ((historyLaw law).historyAt occurrence).relationClosure,
      read (integerToValueWords law
        (installedRelationAction law occurrence relation).1) = 0 := by
  constructor
  · rintro ⟨factor, commutes⟩ relation
    have atBoundary := LinearMap.congr_fun commutes
      (integerToValueWords law
        (installedRelationAction law occurrence relation).1)
    change factor (valueRelationProjection law occurrence
      (integerToValueWords law
        (installedRelationAction law occurrence relation).1)) = _ at atBoundary
    rw [valueRelationProjection_old_boundary, map_zero] at atBoundary
    exact atBoundary.symm
  · intro killed
    have compatible : LinearMap.range (valueRelationAction law occurrence) ≤
        LinearMap.ker read := by
      rw [LinearMap.range_le_ker_iff]
      apply LinearMap.ext
      intro relations
      induction relations using Finsupp.induction_linear with
      | zero => simp
      | add left right left_ih right_ih =>
          simp only [map_add, left_ih, right_ih]
      | single relation coefficient =>
          change read (valueRelationAction law occurrence
            (Finsupp.single relation coefficient)) = 0
          rw [valueRelationAction_single, map_smul, killed relation, smul_zero]
    refine ⟨Submodule.liftQ (LinearMap.range (valueRelationAction law occurrence))
      read compatible, ?_⟩
    apply LinearMap.ext
    intro word
    rfl

theorem valueRelationEvaluation_descent_iff (law : Law D Carrier)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier] Carrier,
      factor.comp (valueRelationProjection law occurrence) =
        valueWordEvaluation law occurrence) ↔
    ∀ relation : ((historyLaw law).historyAt occurrence).relationClosure,
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
        (installedRelationAction law occurrence relation).1 = 0 := by
  constructor
  · intro factor relation
    have zero := (valueRelation_descend_iff law occurrence
      (valueWordEvaluation law occurrence)).mp factor relation
    exact (valueWordEvaluation_integer_square law occurrence _).symm.trans zero
  · intro killed
    apply (valueRelation_descend_iff law occurrence
      (valueWordEvaluation law occurrence)).mpr
    intro relation
    exact (valueWordEvaluation_integer_square law occurrence _).trans
      (killed relation)

theorem valueRelationPairing_descent_iff [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier]
        Module.Dual Carrier (ValueWords law),
      factor.comp (valueRelationProjection law occurrence) =
        valueWordPairing law occurrence) ↔
    ∀ relation : ((historyLaw law).historyAt occurrence).relationClosure,
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
        (installedRelationAction law occurrence relation).1 = 0 := by
  rw [valueRelation_descend_iff]
  constructor
  · intro killed relation
    have kernel := valueWordPairing_kernel_eq_evaluation_kernel law occurrence
    have atRelation := killed relation
    have mem : integerToValueWords law
        (installedRelationAction law occurrence relation).1 ∈
        LinearMap.ker (valueWordPairing law occurrence) := atRelation
    rw [kernel] at mem
    exact (valueWordEvaluation_integer_square law occurrence _).symm.trans mem
  · intro killed relation
    have zero : valueWordEvaluation law occurrence
        (integerToValueWords law
          (installedRelationAction law occurrence relation).1) = 0 :=
      (valueWordEvaluation_integer_square law occurrence _).trans
        (killed relation)
    have mem : integerToValueWords law
        (installedRelationAction law occurrence relation).1 ∈
        LinearMap.ker (valueWordEvaluation law occurrence) := zero
    rw [← valueWordPairing_kernel_eq_evaluation_kernel law occurrence] at mem
    exact mem

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
