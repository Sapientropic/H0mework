import Mathlib.NumberTheory.LSeries.RiemannZeta
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticUnitNormalizedCoordinateRegression
import H0mework.Versions.R2.Arithmetic.EulerLocal.UnitDeterminantAction

/-!
# Classical coordinate regression for the generated Euler determinant

The arithmetic producer is already closed before this file: direct relation
history, all-prime-power rigidity, fixed component, perfect determinant,
Euler/reversal chain action and determinant naturality.

For a complex coordinate `s`, a classical specialization is a linear map
from that actual completion which sends the two generated component classes
to `(1,s)` and `(1,1-conj s)`.  Such a map can be generated from the fixed
coordinate equation, and any such map forces that equation because the two
source classes are already equal.

Thus the final Mathlib statement below is deliberately a regression
equivalence.  It is not accepted by any arithmetic producer mouth and makes
the exact external specialization obligation visible without reintroducing
a coordinate or coverage field upstream.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEulerDeterminantCoordinateRegression

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticDerivedCoordinateRegression
open CanonicalUnitArithmeticUnitNormalizedCoordinateRegression
open CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction
open CanonicalUnitArithmeticUnitNormalizedRelationHistory
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open scoped ComplexConjugate

noncomputable section

def coordinateAtom (coordinate : ℂ) : Generator → UnitCoordinate
  | some (.component, 0) => unitCoordinateGenerator coordinate
  | some (.component, 1) =>
      unitCoordinateGenerator (coordinateReversal coordinate)
  | _ => 0

def freeCoordinateEvaluation (coordinate : ℂ) :
    Lattice →ₗ[ℤ] UnitCoordinate :=
  (Finsupp.liftAddHom fun generator =>
    AddMonoidHom.flip (smulAddHom ℤ UnitCoordinate)
      (coordinateAtom coordinate generator)).toIntLinearMap

@[simp] theorem freeCoordinateEvaluation_single
    (coordinate : ℂ) (generator : Generator) (coefficient : ℤ) :
    freeCoordinateEvaluation coordinate
        (Finsupp.single generator coefficient) =
      coefficient • coordinateAtom coordinate generator := by
  simp [freeCoordinateEvaluation]

theorem freeCoordinateEvaluation_embeddedComponentDifference
    (coordinate : ℂ) :
    freeCoordinateEvaluation coordinate embeddedComponentDifference =
      unitCoordinateGenerator coordinate -
        unitCoordinateGenerator (coordinateReversal coordinate) := by
  unfold embeddedComponentDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference
  calc
    freeCoordinateEvaluation coordinate
        (liftEnvelope
          (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .component 0 -
            CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .component 1)) =
      freeCoordinateEvaluation coordinate
          (liftEnvelope
            (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .component 0)) -
        freeCoordinateEvaluation coordinate
          (liftEnvelope
            (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .component 1)) := by
        rw [map_sub, map_sub]
    _ = unitCoordinateGenerator coordinate -
        unitCoordinateGenerator (coordinateReversal coordinate) := by
      rw [liftEnvelope_basis, liftEnvelope_basis,
        freeCoordinateEvaluation_single,
        freeCoordinateEvaluation_single]
      simp [coordinateAtom]

theorem freeCoordinateEvaluation_embeddedQuotientUnitDifference
    (coordinate : ℂ) :
    freeCoordinateEvaluation coordinate embeddedQuotientUnitDifference = 0 := by
  unfold embeddedQuotientUnitDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference
  calc
    freeCoordinateEvaluation coordinate
        (liftEnvelope
          (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .quotientUnit 0 -
            CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .quotientUnit 1)) =
      freeCoordinateEvaluation coordinate
          (liftEnvelope
            (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .quotientUnit 0)) -
        freeCoordinateEvaluation coordinate
          (liftEnvelope
            (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.basis
              .quotientUnit 1)) := by
        rw [map_sub, map_sub]
    _ = 0 := by
      rw [liftEnvelope_basis, liftEnvelope_basis,
        freeCoordinateEvaluation_single,
        freeCoordinateEvaluation_single]
      simp [coordinateAtom]

@[simp] theorem freeCoordinateEvaluation_clockMarker
    (coordinate : ℂ) (cursor : Nat) :
    freeCoordinateEvaluation coordinate (clockMarker cursor) = 0 := by
  unfold clockMarker
  rw [freeCoordinateEvaluation_single]
  simp [coordinateAtom]

theorem freeCoordinateEvaluation_localRelation_of_fixed
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate)
    (cursor : Nat) :
    freeCoordinateEvaluation coordinate (localRelation cursor) = 0 := by
  rw [localRelation_normalForm, map_sub, map_nsmul, map_nsmul,
    freeCoordinateEvaluation_embeddedComponentDifference,
    freeCoordinateEvaluation_embeddedQuotientUnitDifference]
  rw [fixed]
  have involutive :
      coordinateReversal (coordinateReversal coordinate) = coordinate := by
    unfold coordinateReversal
    apply Complex.ext <;> simp
  rw [involutive]
  rw [← fixed]
  simp

theorem relationClosure_le_coordinateKernel_of_fixed
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate) :
    history.relationClosure ≤
      LinearMap.ker (freeCoordinateEvaluation coordinate) := by
  apply iSup_le
  intro stage
  apply Submodule.span_le.mpr
  intro relationValue relationEvent
  change freeCoordinateEvaluation coordinate relationValue = 0
  rcases
      CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction.observed_relation_generated
        stage relationValue relationEvent with localRow | markerRow
  · obtain ⟨cursor, rfl⟩ := localRow
    exact freeCoordinateEvaluation_localRelation_of_fixed
      coordinate fixed cursor
  · obtain ⟨cursor, rfl⟩ := markerRow
    exact freeCoordinateEvaluation_clockMarker coordinate cursor

def closureCoordinateEvaluation (coordinate : ℂ) :
    history.generatorClosure →ₗ[ℤ] UnitCoordinate :=
  (freeCoordinateEvaluation coordinate).comp
    history.generatorClosure.subtype

theorem relationInGeneratorClosure_le_coordinateKernel_of_fixed
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate) :
    history.relationInGeneratorClosure ≤
      LinearMap.ker (closureCoordinateEvaluation coordinate) := by
  intro relationValue relationMem
  rw [LinearMap.mem_ker]
  exact relationClosure_le_coordinateKernel_of_fixed
    coordinate fixed relationMem

def completionCoordinateEvaluationOfFixed
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate) :
    history.CompletionCarrier →ₗ[ℤ] UnitCoordinate :=
  history.relationInGeneratorClosure.liftQ
    (closureCoordinateEvaluation coordinate)
    (relationInGeneratorClosure_le_coordinateKernel_of_fixed
      coordinate fixed)

@[simp] theorem completionCoordinateEvaluationOfFixed_stageGenerator
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate)
    (stage : Nat) (value : history.generatorStage stage) :
    completionCoordinateEvaluationOfFixed coordinate fixed
        (history.stageGeneratorToCompletion stage value) =
      freeCoordinateEvaluation coordinate value :=
  rfl

theorem completionCoordinateEvaluationOfFixed_componentClass
    (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate)
    (dualIndex : Fin 2) :
    completionCoordinateEvaluationOfFixed coordinate fixed
        (componentClass dualIndex) =
      if dualIndex = 0 then unitCoordinateGenerator coordinate
      else unitCoordinateGenerator (coordinateReversal coordinate) := by
  fin_cases dualIndex <;>
    simp [componentClass, freeCoordinateEvaluation, coordinateAtom]

/-- Exact external coordinate specialization of the already generated
determinant component.  The constructor is private so the two endpoint laws
cannot be omitted. -/
structure CoordinateSpecializationAt (coordinate : ℂ) : Type where
  private mk ::
  evaluation : history.CompletionCarrier →ₗ[ℤ] UnitCoordinate
  original : evaluation (componentClass 0) =
    unitCoordinateGenerator coordinate
  reversed : evaluation (componentClass 1) =
    unitCoordinateGenerator (coordinateReversal coordinate)

def coordinateSpecializationOfFixed (coordinate : ℂ)
    (fixed : coordinate = coordinateReversal coordinate) :
    CoordinateSpecializationAt coordinate :=
  by
    refine ⟨completionCoordinateEvaluationOfFixed coordinate fixed,
      ?_, ?_⟩
    · simpa using completionCoordinateEvaluationOfFixed_componentClass
        coordinate fixed 0
    · simpa using completionCoordinateEvaluationOfFixed_componentClass
        coordinate fixed 1

theorem fixedOfCoordinateSpecialization (coordinate : ℂ)
    (specialization : CoordinateSpecializationAt coordinate) :
    coordinate = coordinateReversal coordinate := by
  have sameSource := congrArg specialization.evaluation
    generatedFixedComponent
  rw [specialization.original, specialization.reversed] at sameSource
  exact congrArg Prod.snd sameSource

theorem coordinateSpecialization_iff_fixed (coordinate : ℂ) :
    Nonempty (CoordinateSpecializationAt coordinate) ↔
      coordinate = coordinateReversal coordinate := by
  constructor
  · rintro ⟨specialization⟩
    exact fixedOfCoordinateSpecialization coordinate specialization
  · intro fixed
    exact ⟨coordinateSpecializationOfFixed coordinate fixed⟩

theorem real_eq_half_of_coordinateSpecialization (coordinate : ℂ)
    (specialization : CoordinateSpecializationAt coordinate) :
    coordinate.re = 1 / 2 := by
  have fixed := fixedOfCoordinateSpecialization coordinate specialization
  have realFixed := congrArg Complex.re fixed
  change coordinate.re = 1 - coordinate.re at realFixed
  linarith

/-- Mathlib RH as the terminal coordinate regression of the actual generated
Euler determinant state. -/
theorem riemannHypothesis_iff_eulerDeterminantCoordinateSpecialization :
    RiemannHypothesis ↔
      ∀ (coordinate : ℂ),
        riemannZeta coordinate = 0 →
        (¬∃ n : Nat, coordinate = -2 * (n + 1)) →
        coordinate ≠ 1 →
        Nonempty (CoordinateSpecializationAt coordinate) := by
  constructor
  · intro rh coordinate zetaZero nontrivial notPole
    exact ⟨coordinateSpecializationOfFixed coordinate <|
      coordinate_fixed_of_real_eq_half coordinate <|
        rh coordinate zetaZero nontrivial notPole⟩
  · intro specializations coordinate zetaZero nontrivial notPole
    exact real_eq_half_of_coordinateSpecialization coordinate
      (specializations coordinate zetaZero nontrivial notPole).some

end

end CanonicalUnitArithmeticEulerDeterminantCoordinateRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
