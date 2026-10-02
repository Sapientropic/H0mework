import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import H0mework.Versions.R2.Arithmetic.EulerGlobal.WholeRelationAction
import H0mework.Realization.FiniteCell.DerivedAction
import H0mework.Realization.FiniteCell.DerivedAdequacy
import H0mework.Realization.FiniteCell.IncidenceAdequacy

/-!
# Derived determinant section of the full-Euler whole relation complex

The actual two-term factorization relation complex is represented directly in
degrees `0` and `1`.  A finite basis frontier is closed under its genuine
differential, so the frozen finite-frontier and derived-action engines generate
the basis-free alternating determinant of the pointwise full-Euler action.

No matrix, determinant polynomial, zero point, quotient root, perfectness
receipt, or cancellation equality is supplied by the caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open CanonicalFrontierDeterminant
open CanonicalFrontierDerivedAction
open CanonicalFrontierActionDeterminant
open FiniteAtomDerivedCofiberAdequacy
open FiniteAtomIncidenceAdequacy
open FiniteAtomIncidenceAdequacy.RootGeneratedFiniteAtomIncidenceAt
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber

noncomputable section

abbrev ZeroCarrier := Fin 0 → ℤ

noncomputable abbrev DirectObject (seed : FactorizationPayload) (stage : Nat)
    (degree : ℤ) : ModuleCat.{0} ℤ :=
  if degree = 0 then VertexObject seed stage
  else if degree = 1 then RelationObject seed stage
  else ModuleCat.of ℤ ZeroCarrier

noncomputable def directDifferential (seed : FactorizationPayload)
    (stage : Nat) (degree : ℤ) :
    DirectObject seed stage degree ⟶ DirectObject seed stage (degree + 1) := by
  by_cases degreeZero : degree = 0
  · subst degree
    exact ModuleCat.ofHom (factorizationDifferential seed stage)
  · exact 0

theorem directDifferential_sq (seed : FactorizationPayload) (stage : Nat)
    (degree : ℤ) :
    directDifferential seed stage degree ≫
        directDifferential seed stage (degree + 1) = 0 := by
  by_cases degreeZero : degree = 0
  · subst degree
    simp [directDifferential]
  · simp [directDifferential, degreeZero]

noncomputable abbrev directComplex (seed : FactorizationPayload) (stage : Nat) :
    IntegralCochainComplex ℤ :=
  CochainComplex.of (DirectObject seed stage)
    (directDifferential seed stage) (directDifferential_sq seed stage)

noncomputable def directEulerAction (seed : FactorizationPayload) (stage : Nat) :
    directComplex seed stage ⟶ directComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (vertexEulerAction seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (relationEulerAction seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      change ModuleCat.ofHom (vertexEulerAction seed stage) ≫
          ModuleCat.ofHom (factorizationDifferential seed stage) =
        ModuleCat.ofHom (factorizationDifferential seed stage) ≫
          ModuleCat.ofHom (relationEulerAction seed stage)
      apply ModuleCat.hom_ext
      exact factorizationDifferential_euler_square seed stage
    · simp [directComplex, directDifferential, sourceZero]

noncomputable def directReversal (seed : FactorizationPayload) (stage : Nat) :
    directComplex seed stage ⟶ directComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
          seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom
          (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
            seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      change ModuleCat.ofHom
          (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
            seed stage) ≫
          ModuleCat.ofHom (factorizationDifferential seed stage) =
        ModuleCat.ofHom (factorizationDifferential seed stage) ≫
          ModuleCat.ofHom
            (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
              seed stage)
      apply ModuleCat.hom_ext
      exact factorizationDifferential_reversal_square seed stage
    · simp [directComplex, directDifferential, sourceZero]

theorem directEuler_reversal_commutes (seed : FactorizationPayload)
    (stage : Nat) :
    directEulerAction seed stage ≫ directReversal seed stage =
      directReversal seed stage ≫ directEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    simpa [directEulerAction, directReversal, DirectObject] using
      (LinearMap.congr_fun (vertexEuler_reversal_commutes seed stage) _).symm
  · by_cases degreeOne : degree = 1
    · subst degree
      simpa [directEulerAction, directReversal, DirectObject] using
        (LinearMap.congr_fun (relationEuler_reversal_commutes seed stage) _).symm
    · simp [directEulerAction, directReversal, degreeZero, degreeOne]

noncomputable def directRestriction (seed : FactorizationPayload) (stage : Nat) :
    directComplex seed (stage + 1) ⟶ directComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (vertexRestriction seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (relationRestriction seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      change ModuleCat.ofHom (vertexRestriction seed stage) ≫
          ModuleCat.ofHom (factorizationDifferential seed stage) =
        ModuleCat.ofHom (factorizationDifferential seed (stage + 1)) ≫
          ModuleCat.ofHom (relationRestriction seed stage)
      apply ModuleCat.hom_ext
      exact factorizationRestriction_differential_square seed stage
    · simp [directComplex, directDifferential, sourceZero]

theorem directRestriction_euler_square (seed : FactorizationPayload)
    (stage : Nat) :
    directEulerAction seed (stage + 1) ≫ directRestriction seed stage =
      directRestriction seed stage ≫ directEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun (vertexRestriction_euler_square seed stage) _
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (relationRestriction_euler_square seed stage) _
    · simp [directEulerAction, directRestriction, degreeZero, degreeOne]

theorem directRestriction_reversal_square (seed : FactorizationPayload)
    (stage : Nat) :
    directReversal seed (stage + 1) ≫ directRestriction seed stage =
      directRestriction seed stage ≫ directReversal seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (vertexRestriction_reversal_square seed stage) _
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (relationRestriction_reversal_square seed stage) _
    · simp [directReversal, directRestriction, degreeZero, degreeOne]

variable (seed : FactorizationPayload) (stage : Nat)

def complexOccurrence : RootedAccountedUnfolding (IntegralCochainComplex ℤ) :=
  RootedAccountedUnfolding.zero (directComplex seed stage)

def compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
    (stageOccurrenceFrom seed stage) (complexOccurrence seed stage) :=
  RootGeneratedCanonicalFiniteFrontierCompressionAt.generate

noncomputable instance directComplex_zero_free :
    Module.Free ℤ ((compression seed stage).actualComplex.X 0) := by
  change Module.Free ℤ (WholeVertexModule seed stage)
  infer_instance

noncomputable instance directComplex_zero_finite :
    Module.Finite ℤ ((compression seed stage).actualComplex.X 0) := by
  change Module.Finite ℤ (WholeVertexModule seed stage)
  infer_instance

noncomputable instance directComplex_one_free :
    Module.Free ℤ ((compression seed stage).actualComplex.X 1) := by
  change Module.Free ℤ (WholeRelationModule seed stage)
  infer_instance

noncomputable instance directComplex_one_finite :
    Module.Finite ℤ ((compression seed stage).actualComplex.X 1) := by
  change Module.Finite ℤ (WholeRelationModule seed stage)
  infer_instance

abbrev VertexBasisIndex :=
  Fin (Module.finrank ℤ (WholeVertexModule seed stage))

abbrev RelationBasisIndex :=
  Fin (Module.finrank ℤ (WholeRelationModule seed stage))

noncomputable def vertexBasis :
    Module.Basis (VertexBasisIndex seed stage) ℤ
      (WholeVertexModule seed stage) :=
  Module.finBasis ℤ (WholeVertexModule seed stage)

noncomputable def relationBasis :
    Module.Basis (RelationBasisIndex seed stage) ℤ
      (WholeRelationModule seed stage) :=
  Module.finBasis ℤ (WholeRelationModule seed stage)

def zeroAtom : ActualCochainAtomAt (compression seed stage).actualComplex :=
  ⟨0, 0⟩

def vertexAtom (index : VertexBasisIndex seed stage) :
    ActualCochainAtomAt (compression seed stage).actualComplex :=
  ⟨0, vertexBasis seed stage index⟩

def relationAtom (index : RelationBasisIndex seed stage) :
    ActualCochainAtomAt (compression seed stage).actualComplex :=
  ⟨1, relationBasis seed stage index⟩

local instance : DecidableEq
    (ActualCochainAtomAt (compression seed stage).actualComplex) :=
  Classical.decEq _

noncomputable def basisFrontier :
    CanonicalFiniteFrontierAt (compression seed stage).actualComplex :=
  {zeroAtom seed stage} ∪
    (Finset.univ.image (vertexAtom seed stage) ∪
      Finset.univ.image (relationAtom seed stage))

noncomputable def closedFrontier :
    CanonicalFiniteFrontierAt (compression seed stage).actualComplex :=
  differentialClosure (basisFrontier seed stage)

private def atomBranches (seed : FactorizationPayload) (stage : Nat) :
    List (ActualCochainAtomAt (compression seed stage).actualComplex) →
      AccountedBranches
        (ActualCochainAtomAt (compression seed stage).actualComplex)
  | [] => .nil
  | atom :: tail => .cons (.zero atom) (atomBranches seed stage tail)

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
    (atomBranches seed stage (closedFrontier seed stage).toList)

def incidence : RootGeneratedFiniteAtomIncidenceAt
    (compression seed stage) (atomOccurrence seed stage) :=
  RootGeneratedFiniteAtomIncidenceAt.generate

theorem zeroAtom_mem_basisFrontier :
    zeroAtom seed stage ∈ basisFrontier seed stage := by
  simp [basisFrontier]

theorem zeroAtom_mem_closedFrontier :
    zeroAtom seed stage ∈ closedFrontier seed stage := by
  apply Finset.mem_union_left
  exact zeroAtom_mem_basisFrontier seed stage

theorem incidence_frontier_eq_closedFrontier :
    (incidence seed stage).frontier = closedFrontier seed stage := by
  unfold RootGeneratedFiniteAtomIncidenceAt.frontier atomOccurrence
  change (zeroAtom seed stage ::
      RootedAccountedUnfolding.traceBranches
        (atomBranches seed stage (closedFrontier seed stage).toList)).toFinset = _
  rw [traceBranches_atomBranches]
  simp [zeroAtom_mem_closedFrontier seed stage]

theorem vertexAtom_mem_frontier (index : VertexBasisIndex seed stage) :
    vertexAtom seed stage index ∈ (incidence seed stage).frontier := by
  rw [incidence_frontier_eq_closedFrontier]
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩

theorem relationAtom_mem_frontier (index : RelationBasisIndex seed stage) :
    relationAtom seed stage index ∈ (incidence seed stage).frontier := by
  rw [incidence_frontier_eq_closedFrontier]
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩

def vertexGenerator (index : VertexBasisIndex seed stage) :
    StageGeneratorAt (incidence seed stage).frontier 0 :=
  ⟨⟨vertexAtom seed stage index, vertexAtom_mem_frontier seed stage index⟩,
    rfl⟩

def relationGenerator (index : RelationBasisIndex seed stage) :
    StageGeneratorAt (incidence seed stage).frontier 1 :=
  ⟨⟨relationAtom seed stage index,
    relationAtom_mem_frontier seed stage index⟩, rfl⟩

@[simp] theorem vertexGenerator_actualValue
    (index : VertexBasisIndex seed stage) :
    StageGeneratorAt.actualValue (vertexGenerator seed stage index) =
      vertexBasis seed stage index := by
  rfl

@[simp] theorem relationGenerator_actualValue
    (index : RelationBasisIndex seed stage) :
    StageGeneratorAt.actualValue (relationGenerator seed stage index) =
      relationBasis seed stage index := by
  rfl

theorem incidence_spans :
    DegreewiseSpansActualCarrier (incidence seed stage).frontier := by
  intro degree value
  by_cases degreeZero : degree = 0
  · subst degree
    let coordinates := (vertexBasis seed stage).repr value
    let preimage : StageFreeModuleAt (incidence seed stage).frontier 0 :=
      ∑ index : VertexBasisIndex seed stage,
        Finsupp.single (vertexGenerator seed stage index) (coordinates index)
    refine ⟨preimage, ?_⟩
    unfold preimage
    rw [map_sum]
    have single_eq_smul (index : VertexBasisIndex seed stage) :
        Finsupp.single (vertexGenerator seed stage index) (coordinates index) =
          coordinates index •
            Finsupp.single (vertexGenerator seed stage index) 1 := by
      ext generator
      simp
    simp_rw [single_eq_smul, map_smul, stageEvaluation_single_one]
    simpa only [vertexGenerator_actualValue] using
      (vertexBasis seed stage).sum_repr value
  · by_cases degreeOne : degree = 1
    · subst degree
      let coordinates := (relationBasis seed stage).repr value
      let preimage : StageFreeModuleAt (incidence seed stage).frontier 1 :=
        ∑ index : RelationBasisIndex seed stage,
          Finsupp.single (relationGenerator seed stage index)
            (coordinates index)
      refine ⟨preimage, ?_⟩
      unfold preimage
      rw [map_sum]
      have single_eq_smul (index : RelationBasisIndex seed stage) :
          Finsupp.single (relationGenerator seed stage index)
              (coordinates index) =
            coordinates index •
              Finsupp.single (relationGenerator seed stage index) 1 := by
        ext generator
        simp
      simp_rw [single_eq_smul, map_smul, stageEvaluation_single_one]
      simpa only [relationGenerator_actualValue] using
        (relationBasis seed stage).sum_repr value
    · refine ⟨0, ?_⟩
      have targetSubsingleton :
          Subsingleton ((compression seed stage).actualComplex.X degree) := by
        change Subsingleton (DirectObject seed stage degree)
        simp [DirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

theorem incidence_differentialCovered :
    DifferentialCoveredAt (incidence seed stage).frontier := by
  rw [incidence_frontier_eq_closedFrontier]
  exact differentialClosure_covered (basisFrontier seed stage)

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

def actionOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      ((compression seed stage).actualComplex ⟶
        (compression seed stage).actualComplex)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, directEulerAction seed stage)

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

/-- Split the unique whole slot from the quotient-row slots. -/
def vertexEquivWholeRelation :
    WholeVertexModule seed stage ≃ₗ[ℤ]
      InnerCarrier seed stage × WholeRelationModule seed stage where
  toFun value := (value none, fun row => value (some row))
  invFun value role :=
    match role with
    | none => value.1
    | some row => value.2 row
  map_add' := by
    intro left right
    apply Prod.ext
    · rfl
    · funext row
      rfl
  map_smul' := by
    intro scalar value
    apply Prod.ext
    · rfl
    · funext row
      rfl
  left_inv value := by
    funext role
    cases role <;> rfl
  right_inv value := by
    rcases value with ⟨whole, quotient⟩
    rfl

theorem vertexEulerAction_conj_eq_prodMap :
    (vertexEquivWholeRelation seed stage).conj
        (vertexEulerAction seed stage) =
      (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEulerAction
        seed stage).prodMap
        (relationEulerAction seed stage) := by
  apply LinearMap.ext
  intro value
  rcases value with ⟨whole, quotient⟩
  apply Prod.ext
  · rfl
  · funext row
    rfl

theorem vertexEulerAction_charpoly_eq_product :
    (vertexEulerAction seed stage).charpoly =
      (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEulerAction
        seed stage).charpoly *
        (relationEulerAction seed stage).charpoly := by
  have conjugation := LinearEquiv.charpoly_conj
    (vertexEquivWholeRelation seed stage) (vertexEulerAction seed stage)
  rw [vertexEulerAction_conj_eq_prodMap] at conjugation
  calc
    (vertexEulerAction seed stage).charpoly =
        ((CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEulerAction
          seed stage).prodMap
          (relationEulerAction seed stage)).charpoly := conjugation.symm
    _ = (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEulerAction
          seed stage).charpoly *
          (relationEulerAction seed stage).charpoly :=
      LinearMap.charpoly_prodMap _ _

noncomputable def innerEulerDeterminantPolynomial : Polynomial ℤ :=
  (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEulerAction
    seed stage).charpoly.reverse

noncomputable def vertexEulerDeterminantPolynomial : Polynomial ℤ :=
  (vertexEulerAction seed stage).charpoly.reverse

noncomputable def relationEulerDeterminantPolynomial : Polynomial ℤ :=
  (relationEulerAction seed stage).charpoly.reverse

/-- Actual alternating action readout before any coordinate specialization. -/
noncomputable def actualAlternatingFraction : IntegralDeterminantFractionAt :=
  ⟨vertexEulerDeterminantPolynomial seed stage,
    relationEulerDeterminantPolynomial seed stage⟩

/-- Quotient/relation copies cancel in the alternating determinant, leaving
exactly one copy of the prime-sensitive inner full-Euler determinant. -/
theorem vertexDeterminant_eq_inner_mul_relationDeterminant :
    vertexEulerDeterminantPolynomial seed stage =
      innerEulerDeterminantPolynomial seed stage *
        relationEulerDeterminantPolynomial seed stage := by
  unfold vertexEulerDeterminantPolynomial innerEulerDeterminantPolynomial
    relationEulerDeterminantPolynomial
  rw [vertexEulerAction_charpoly_eq_product,
    Polynomial.reverse_mul_of_domain]

theorem actualAlternatingFraction_cancels_to_inner :
    (actualAlternatingFraction seed stage).numerator =
      innerEulerDeterminantPolynomial seed stage *
        (actualAlternatingFraction seed stage).denominator :=
  vertexDeterminant_eq_inner_mul_relationDeterminant seed stage

theorem derivedAction_reads_directEulerAction :
    (derivedAction seed stage).actualAction = directEulerAction seed stage := by
  simpa [actionOccurrence] using
    (derivedAction seed stage).preserves_actual_action_and_derived_conjugation.1

theorem frozenActualAction_degree_zero_reads_vertex :
    (((derivedAction seed stage).actualAction.f 0).hom.charpoly.reverse) =
      vertexEulerDeterminantPolynomial seed stage := by
  rw [derivedAction_reads_directEulerAction]
  rfl

theorem frozenActualAction_degree_one_reads_relation :
    (((derivedAction seed stage).actualAction.f 1).hom.charpoly.reverse) =
      relationEulerDeterminantPolynomial seed stage := by
  rw [derivedAction_reads_directEulerAction]
  rfl

theorem determinantFraction_constant_coefficients :
    (determinantFraction seed stage).numerator.coeff 0 = 1 ∧
      (determinantFraction seed stage).denominator.coeff 0 = 1 :=
  (derivedAction seed stage).actionDeterminant.determinantFraction_coeff_zero

theorem preserves_exact_root_relation_complex_and_generated_determinant :
    (determinantFace seed stage).root =
        stageOccurrenceFrom seed stage ∧
      (actionOccurrence seed stage).root.2 = directEulerAction seed stage ∧
      (determinantFraction seed stage).numerator.coeff 0 = 1 ∧
      (determinantFraction seed stage).denominator.coeff 0 = 1 := by
  exact ⟨rfl, by simp [actionOccurrence],
    determinantFraction_constant_coefficients seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
