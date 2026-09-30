import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.StdBasis
import H0mework.Versions.X.Arithmetic.EulerGlobal.SolutionAction
import H0mework.Realization.FiniteCell.DerivedAction
import H0mework.Realization.FiniteCell.IncidenceAdequacy

/-!
# Full-Euler derived determinant section

The actual carrier is the integral solution module of the exponent-successor
Euler relations, not the unreduced exponent lattice.  Its finite basis is
generated from the recurrence's initial-value equivalence.  The standard
finite atom trace feeds the frozen canonical-frontier derived-action engine;
the same action occurrence also generates the basis-free polynomial section
`det(1 - X F)`.

The resulting section visibly reads every actual prime.  Exponent duplicates
have already been removed by the actual recurrence kernel, while both members
of the reversal orbit are retained and counted.  No determinant polynomial,
basis, matrix, zero, coordinate evaluator, coverage, fixedness, or completed
cofinal family is accepted from a caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open CanonicalFrontierDeterminant
open CanonicalFrontierDerivedAction
open CanonicalFrontierActionDeterminant
open FiniteAtomIncidenceAdequacy
open FiniteAtomIncidenceAdequacy.RootGeneratedFiniteAtomIncidenceAt
open CategoryTheory
open DerivedAdicCofiber
open Polynomial

noncomputable section

variable (seed : FactorizationPayload) (stage : Nat)

abbrev ZeroCarrier := Fin 0 → ℤ

abbrev ActualComplex : IntegralCochainComplex ℤ where
  X degree := if degree = 0 then
    ModuleCat.of ℤ (Carrier seed stage)
  else
    ModuleCat.of ℤ ZeroCarrier
  d _source _target := 0

abbrev complexOccurrence : RootedAccountedUnfolding
    (IntegralCochainComplex ℤ) :=
  RootedAccountedUnfolding.zero (ActualComplex seed stage)

abbrev compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
    (stageOccurrenceFrom seed stage) (complexOccurrence seed stage) :=
  RootGeneratedCanonicalFiniteFrontierCompressionAt.generate

noncomputable instance actualComplex_zero_free :
    Module.Free ℤ ((compression seed stage).actualComplex.X 0) := by
  change Module.Free ℤ (Carrier seed stage)
  infer_instance

noncomputable instance actualComplex_zero_finite :
    Module.Finite ℤ ((compression seed stage).actualComplex.X 0) := by
  change Module.Finite ℤ (Carrier seed stage)
  infer_instance

noncomputable def solutionBasis :
    Module.Basis (BaseIndex seed stage) ℤ (Carrier seed stage) :=
  (Pi.basisFun ℤ (BaseIndex seed stage)).map
    (carrierEquivBase seed stage).symm

def zeroAtom : ActualCochainAtomAt (compression seed stage).actualComplex :=
  ⟨0, 0⟩

def basisAtom (index : BaseIndex seed stage) :
    ActualCochainAtomAt (compression seed stage).actualComplex :=
  ⟨0, solutionBasis seed stage index⟩

private def atomBranches :
    List (ActualCochainAtomAt (compression seed stage).actualComplex) →
      AccountedBranches
        (ActualCochainAtomAt (compression seed stage).actualComplex)
  | [] => .nil
  | atom :: tail => .cons (.zero atom) (atomBranches tail)

private theorem traceBranches_atomBranches
    (atoms : List (ActualCochainAtomAt
      (compression seed stage).actualComplex)) :
    RootedAccountedUnfolding.traceBranches (atomBranches seed stage atoms) =
      atoms := by
  induction atoms with
  | nil => rfl
  | cons atom tail inductionHypothesis =>
      change atom :: [] ++
          RootedAccountedUnfolding.traceBranches
            (atomBranches seed stage tail) = atom :: tail
      rw [inductionHypothesis]
      rfl

def atomOccurrence : RootedAccountedUnfolding
    (ActualCochainAtomAt (compression seed stage).actualComplex) :=
  .occur (zeroAtom seed stage)
    (atomBranches seed stage
      ((Finset.univ : Finset (BaseIndex seed stage)).toList.map
        (basisAtom seed stage)))

local instance : DecidableEq
    (ActualCochainAtomAt (compression seed stage).actualComplex) :=
  Classical.decEq _

theorem basisAtom_mem_trace (index : BaseIndex seed stage) :
    basisAtom seed stage index ∈ (atomOccurrence seed stage).trace := by
  change basisAtom seed stage index ∈
    zeroAtom seed stage ::
      RootedAccountedUnfolding.traceBranches
        (atomBranches seed stage
          ((Finset.univ : Finset (BaseIndex seed stage)).toList.map
            (basisAtom seed stage)))
  rw [traceBranches_atomBranches]
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  exact ⟨index, Finset.mem_toList.mpr (Finset.mem_univ index), rfl⟩

def incidence : RootGeneratedFiniteAtomIncidenceAt
    (compression seed stage) (atomOccurrence seed stage) :=
  RootGeneratedFiniteAtomIncidenceAt.generate

theorem basisAtom_mem_frontier (index : BaseIndex seed stage) :
    basisAtom seed stage index ∈ (incidence seed stage).frontier := by
  apply List.mem_toFinset.mpr
  exact basisAtom_mem_trace seed stage index

def basisGenerator (index : BaseIndex seed stage) :
    StageGeneratorAt (incidence seed stage).frontier 0 :=
  ⟨⟨basisAtom seed stage index, basisAtom_mem_frontier seed stage index⟩, rfl⟩

@[simp] theorem basisGenerator_actualValue
    (index : BaseIndex seed stage) :
    StageGeneratorAt.actualValue (basisGenerator seed stage index) =
      solutionBasis seed stage index := by
  rfl

theorem incidence_spans :
    DegreewiseSpansActualCarrier (incidence seed stage).frontier := by
  intro degree value
  by_cases degreeZero : degree = 0
  · subst degree
    let coordinates := (solutionBasis seed stage).repr value
    let preimage : StageFreeModuleAt (incidence seed stage).frontier 0 :=
      ∑ index : BaseIndex seed stage,
        Finsupp.single (basisGenerator seed stage index) (coordinates index)
    refine ⟨preimage, ?_⟩
    unfold preimage
    rw [map_sum]
    have single_eq_smul (index : BaseIndex seed stage) :
        Finsupp.single (basisGenerator seed stage index) (coordinates index) =
          coordinates index •
            Finsupp.single (basisGenerator seed stage index) 1 := by
      ext generator
      simp
    simp_rw [single_eq_smul, map_smul, stageEvaluation_single_one]
    simpa only [basisGenerator_actualValue] using
      (solutionBasis seed stage).sum_repr value
  · refine ⟨0, ?_⟩
    let targetSubsingleton : Subsingleton
        ((compression seed stage).actualComplex.X degree) := by
      dsimp [compression,
        RootGeneratedCanonicalFiniteFrontierCompressionAt.actualComplex,
        complexOccurrence, ActualComplex,
        RootedAccountedUnfolding.root,
        RootedAccountedUnfolding.zero]
      rw [if_neg degreeZero]
      infer_instance
    exact @Subsingleton.elim _ targetSubsingleton _ _

theorem incidence_differentialCovered :
    DifferentialCoveredAt (incidence seed stage).frontier := by
  intro source target related generator
  dsimp only
  intro imageNonzero
  exfalso
  apply imageNonzero
  change (0 : (compression seed stage).actualComplex.X target) = 0
  rfl

theorem incidence_calculation :
    (incidence seed stage).AdequacyCalculation :=
  ⟨incidence_spans seed stage, incidence_differentialCovered seed stage⟩

noncomputable def generatedCalculation :
    GeneratedAdequacyCalculationAt (incidence seed stage) := by
  cases (incidence seed stage).settle with
  | inl calculation => exact calculation
  | inr obstruction =>
      exact False.elim (obstruction.persists (incidence_calculation seed stage))

noncomputable def settlement :
    ClassifiedAdequateFrontierAt (compression seed stage) :=
  (incidence seed stage).adequateFrontier (generatedCalculation seed stage)

def determinantFace : RootGeneratedCanonicalFrontierDeterminantAt
    (compression seed stage) (settlement seed stage) :=
  RootGeneratedCanonicalFrontierDeterminantAt.generate

def actualEulerAction :
    (compression seed stage).actualComplex ⟶
      (compression seed stage).actualComplex where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (carrierEulerAction seed stage)
    · exact 0
  comm' _source _target _relation := by
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

def actualReversalAction :
    (compression seed stage).actualComplex ⟶
      (compression seed stage).actualComplex where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (carrierReversal seed stage)
    · exact 0
  comm' _source _target _relation := by
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

theorem actualEuler_reversal_commutes :
    actualEulerAction seed stage ≫ actualReversalAction seed stage =
      actualReversalAction seed stage ≫ actualEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (carrierEuler_reversal_commutes seed stage) _
  · simp [actualEulerAction, actualReversalAction, degreeZero]

def actionOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      ((compression seed stage).actualComplex ⟶
        (compression seed stage).actualComplex)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, actualEulerAction seed stage)

theorem actionOccurrence_projects :
    (actionOccurrence seed stage).map Prod.fst =
      (determinantFace seed stage).root := by
  unfold actionOccurrence determinantFace compression
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

noncomputable def derivedAction :
    RootGeneratedCanonicalFrontierDerivedActionAt
      (determinantFace seed stage) (actionOccurrence seed stage)
        (actionOccurrence_projects seed stage) :=
  RootGeneratedCanonicalFrontierDerivedActionAt.generate

noncomputable def determinantFraction : IntegralDeterminantFractionAt :=
  (derivedAction seed stage).actionDeterminant.determinantFraction

/-- The polynomial section is generated by reading the same actual action
occurrence; no polynomial is present in the caller mouth. -/
noncomputable def determinantPolynomial : Polynomial ℤ :=
  (carrierEulerAction seed stage).charpoly.reverse

def baseEulerAction : BaseLattice seed stage →ₗ[ℤ]
    BaseLattice seed stage where
  toFun := fun value index =>
    actualPrimeScalar seed stage index.1 * value index
  map_add' := by intro left right; funext index; exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem carrierEulerAction_conj_eq_baseEulerAction :
    (carrierEquivBase seed stage).conj (carrierEulerAction seed stage) =
      baseEulerAction seed stage := by
  apply LinearMap.ext
  intro value
  funext index
  rw [LinearEquiv.conj_apply]
  change baseRead seed stage
      (carrierEulerAction seed stage
        (solutionOfBase seed stage value)) index =
    baseEulerAction seed stage value index
  rcases index with ⟨primeIndex, dualIndex⟩
  simp [baseRead, carrierEulerAction, solutionOfBase, extendFromBase,
    exponentZero, baseEulerAction, vertexEulerAction]

theorem carrierEulerAction_charpoly_eq_baseEulerAction :
    (carrierEulerAction seed stage).charpoly =
      (baseEulerAction seed stage).charpoly := by
  have conjugation := LinearEquiv.charpoly_conj
    (carrierEquivBase seed stage) (carrierEulerAction seed stage)
  rw [carrierEulerAction_conj_eq_baseEulerAction] at conjugation
  exact conjugation.symm

theorem baseEulerAction_toMatrix :
    LinearMap.toMatrix
        (Pi.basisFun ℤ (BaseIndex seed stage))
        (Pi.basisFun ℤ (BaseIndex seed stage))
        (baseEulerAction seed stage) =
      Matrix.diagonal
        (fun index : BaseIndex seed stage =>
          actualPrimeScalar seed stage index.1) := by
  ext row column
  by_cases same : row = column
  · subst column
    simp [baseEulerAction]
  · simp [baseEulerAction, same]

theorem baseEulerAction_charpoly :
    (baseEulerAction seed stage).charpoly =
      ∏ index : BaseIndex seed stage,
        (X - C (actualPrimeScalar seed stage index.1)) := by
  rw [← LinearMap.charpoly_toMatrix
    (baseEulerAction seed stage)
      (Pi.basisFun ℤ (BaseIndex seed stage)),
    baseEulerAction_toMatrix, Matrix.charpoly_diagonal]

def localEulerDeterminantFactor (index : BaseIndex seed stage) :
    Polynomial ℤ :=
  1 - X * C (actualPrimeScalar seed stage index.1)

theorem reverse_X_sub_C_actualPrimeScalar
    (index : BaseIndex seed stage) :
    (X - C (actualPrimeScalar seed stage index.1)).reverse =
      localEulerDeterminantFactor seed stage index := by
  have reverseOne : (1 : Polynomial ℤ).reverse = 1 := by
    simpa using (reverse_C (R := ℤ) (1 : ℤ))
  have reverseX : (X : Polynomial ℤ).reverse = 1 := by
    calc
      (X : Polynomial ℤ).reverse = (X * 1).reverse := by rw [mul_one]
      _ = (1 : Polynomial ℤ).reverse := reverse_X_mul 1
      _ = 1 := reverseOne
  calc
    (X - C (actualPrimeScalar seed stage index.1)).reverse =
        (X + C (-actualPrimeScalar seed stage index.1)).reverse := by
      simp [sub_eq_add_neg]
    _ = X.reverse + C (-actualPrimeScalar seed stage index.1) *
        X ^ X.natDegree :=
      reverse_add_C X (-actualPrimeScalar seed stage index.1)
    _ = localEulerDeterminantFactor seed stage index := by
      simp [reverseX, localEulerDeterminantFactor, sub_eq_add_neg]
      ring

theorem reverse_eulerFactors
    (indices : Finset (BaseIndex seed stage)) :
    (∏ index ∈ indices,
      (X - C (actualPrimeScalar seed stage index.1))).reverse =
        ∏ index ∈ indices,
          localEulerDeterminantFactor seed stage index := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using (reverse_C (R := ℤ) (1 : ℤ))
  | @insert index indices fresh inductionHypothesis =>
      rw [Finset.prod_insert fresh, Finset.prod_insert fresh,
        Polynomial.reverse_mul_of_domain,
        reverse_X_sub_C_actualPrimeScalar, inductionHypothesis]

theorem determinantPolynomial_eq_actual_product :
    determinantPolynomial seed stage =
      ∏ index : BaseIndex seed stage,
        localEulerDeterminantFactor seed stage index := by
  rw [determinantPolynomial,
    carrierEulerAction_charpoly_eq_baseEulerAction,
    baseEulerAction_charpoly]
  exact reverse_eulerFactors seed stage Finset.univ

@[simp] theorem determinantPolynomial_coeff_zero :
    (determinantPolynomial seed stage).coeff 0 = 1 := by
  letI : Module.Free ℤ (Carrier seed stage) := inferInstance
  letI : Module.Finite ℤ (Carrier seed stage) := inferInstance
  change ((carrierEulerAction seed stage).charpoly.reverse).coeff 0 = 1
  rw [Polynomial.coeff_zero_reverse]
  exact (LinearMap.charpoly_monic
    (carrierEulerAction seed stage)).leadingCoeff

theorem determinantPolynomial_reads_frozen_actualAction :
    determinantPolynomial seed stage =
      (((derivedAction seed stage).actualAction.f 0).hom.charpoly.reverse) := by
  have actual :=
    (derivedAction seed stage).preserves_actual_action_and_derived_conjugation.1
  have actual' : (derivedAction seed stage).actualAction =
      actualEulerAction seed stage := by
    simpa [actionOccurrence] using actual
  rw [actual']
  rfl

theorem determinantFraction_coeff_zero :
    (determinantFraction seed stage).numerator.coeff 0 = 1 ∧
      (determinantFraction seed stage).denominator.coeff 0 = 1 :=
  (derivedAction seed stage).actionDeterminant.determinantFraction_coeff_zero

theorem preserves_exact_root_relation_action_and_reversal :
    (determinantFace seed stage).root = stageOccurrenceFrom seed stage ∧
      (derivedAction seed stage).actualAction = actualEulerAction seed stage ∧
      actualEulerAction seed stage ≫ actualReversalAction seed stage =
        actualReversalAction seed stage ≫ actualEulerAction seed stage := by
  refine ⟨rfl, ?_, actualEuler_reversal_commutes seed stage⟩
  simpa [actionOccurrence] using
    (derivedAction seed stage).preserves_actual_action_and_derived_conjugation.1

end
end CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
