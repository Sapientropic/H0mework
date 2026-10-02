import Mathlib.LinearAlgebra.Determinant
import H0mework.Versions.R2.Arithmetic.EulerDerived.DeterminantSection
import H0mework.Realization.Arithmetic.DerivedAdicCofiber

/-!
# Whole-relation determinant of the prime-dual block action

The block determinant is calculated again at its true derived mouth: the
degree-zero whole vertex action and degree-one relation action on one exact
two-term complex.  Their canonical `LinearMap.det (1-F)` values cancel by
the actual `Option FactorRow` decomposition, leaving exactly the previously
generated inner block section.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open DerivedAdicCofiber
open CategoryTheory

noncomputable section

noncomputable local instance blockInnerModuleFree
    (seed : FactorizationPayload) (stage : Nat) :
    Module.Free BlockCoordinateRing (BlockInner seed stage) :=
  Module.Free.of_basis
    (Pi.basisFun BlockCoordinateRing (BaseIndex seed stage))

noncomputable local instance blockInnerModuleFinite
    (seed : FactorizationPayload) (stage : Nat) :
    Module.Finite BlockCoordinateRing (BlockInner seed stage) :=
  Module.Finite.of_basis
    (Pi.basisFun BlockCoordinateRing (BaseIndex seed stage))

def blockWholeVertexEulerOperator
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seed stage :=
  LinearMap.id - blockWholeVertexAction seed stage

def blockWholeRelationEulerOperator
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage :=
  LinearMap.id - blockWholeRelationAction seed stage

def blockWholeVertexEulerOperatorPi
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seed stage :=
  LinearMap.pi fun role =>
    (blockEulerOperator seed stage).comp (LinearMap.proj role)

def blockWholeRelationEulerOperatorPi
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage :=
  LinearMap.pi fun row =>
    (blockEulerOperator seed stage).comp (LinearMap.proj row)

theorem blockWholeVertexEulerOperator_eq_pi
    (seed : FactorizationPayload) (stage : Nat) :
    blockWholeVertexEulerOperator seed stage =
      blockWholeVertexEulerOperatorPi seed stage := by
  apply LinearMap.ext
  intro value
  funext role index
  simp [blockWholeVertexEulerOperator, blockWholeVertexEulerOperatorPi,
    blockWholeVertexAction, blockEulerOperator, blockInnerAction]

theorem blockWholeRelationEulerOperator_eq_pi
    (seed : FactorizationPayload) (stage : Nat) :
    blockWholeRelationEulerOperator seed stage =
      blockWholeRelationEulerOperatorPi seed stage := by
  apply LinearMap.ext
  intro value
  funext row index
  simp [blockWholeRelationEulerOperator, blockWholeRelationEulerOperatorPi,
    blockWholeRelationAction, blockEulerOperator, blockInnerAction]

noncomputable def blockWholeVertexDeterminant
    (seed : FactorizationPayload) (stage : Nat) : BlockCoordinateRing :=
  LinearMap.det (blockWholeVertexEulerOperator seed stage)

noncomputable def blockWholeRelationDeterminant
    (seed : FactorizationPayload) (stage : Nat) : BlockCoordinateRing :=
  LinearMap.det (blockWholeRelationEulerOperator seed stage)

theorem blockWholeVertexDeterminant_eq_product
    (seed : FactorizationPayload) (stage : Nat) :
    blockWholeVertexDeterminant seed stage =
      ∏ _role : WholeRole seed stage,
        blockDeterminantSection seed stage := by
  rw [blockWholeVertexDeterminant, blockWholeVertexEulerOperator_eq_pi,
    blockWholeVertexEulerOperatorPi, LinearMap.det_pi]
  apply Finset.prod_congr rfl
  intro role _membership
  rfl

theorem blockWholeRelationDeterminant_eq_product
    (seed : FactorizationPayload) (stage : Nat) :
    blockWholeRelationDeterminant seed stage =
      ∏ _row : FactorRow seed stage,
        blockDeterminantSection seed stage := by
  rw [blockWholeRelationDeterminant, blockWholeRelationEulerOperator_eq_pi,
    blockWholeRelationEulerOperatorPi, LinearMap.det_pi]
  apply Finset.prod_congr rfl
  intro row _membership
  rfl

theorem blockWholeVertexDeterminant_eq_inner_mul_relation
    (seed : FactorizationPayload) (stage : Nat) :
    blockWholeVertexDeterminant seed stage =
      blockDeterminantSection seed stage *
        blockWholeRelationDeterminant seed stage := by
  rw [blockWholeVertexDeterminant_eq_product,
    blockWholeRelationDeterminant_eq_product]
  exact Fintype.prod_option _

structure BlockWholeAlternatingDeterminantAt : Type where
  numerator : BlockCoordinateRing
  denominator : BlockCoordinateRing

noncomputable def blockWholeAlternatingDeterminant
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeAlternatingDeterminantAt :=
  ⟨blockWholeVertexDeterminant seed stage,
    blockWholeRelationDeterminant seed stage⟩

theorem blockWholeAlternatingDeterminant_cancels_to_inner
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeAlternatingDeterminant seed stage).numerator =
      blockDeterminantSection seed stage *
        (blockWholeAlternatingDeterminant seed stage).denominator :=
  blockWholeVertexDeterminant_eq_inner_mul_relation seed stage

/-! ## The exact two-term block complex and its action -/

abbrev BlockZeroCarrier := Fin 0 → BlockCoordinateRing

noncomputable abbrev BlockDirectObject
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    ModuleCat BlockCoordinateRing :=
  if degree = 0 then ModuleCat.of BlockCoordinateRing (BlockWholeVertex seed stage)
  else if degree = 1 then
    ModuleCat.of BlockCoordinateRing (BlockWholeRelation seed stage)
  else ModuleCat.of BlockCoordinateRing BlockZeroCarrier

noncomputable def blockDirectDifferential
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    BlockDirectObject seed stage degree ⟶
      BlockDirectObject seed stage (degree + 1) := by
  by_cases degreeZero : degree = 0
  · subst degree
    exact ModuleCat.ofHom (blockFactorizationDifferential seed stage)
  · exact 0

theorem blockDirectDifferential_sq
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    blockDirectDifferential seed stage degree ≫
        blockDirectDifferential seed stage (degree + 1) = 0 := by
  by_cases degreeZero : degree = 0
  · subst degree
    simp [blockDirectDifferential]
  · simp [blockDirectDifferential, degreeZero]

noncomputable abbrev blockDirectComplex
    (seed : FactorizationPayload) (stage : Nat) :
    IntegralCochainComplex BlockCoordinateRing :=
  CochainComplex.of (BlockDirectObject seed stage)
    (blockDirectDifferential seed stage)
    (blockDirectDifferential_sq seed stage)

noncomputable def blockDirectEulerAction
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectComplex seed stage ⟶ blockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexAction seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationAction seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      exact blockFactorizationDifferential_action_square seed stage
    · simp [blockDirectComplex, blockDirectDifferential, sourceZero]

noncomputable def blockDirectReversal
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectComplex seed stage ⟶ blockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexReversal seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationReversal seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      exact blockFactorizationDifferential_reversal_square seed stage
    · simp [blockDirectComplex, blockDirectDifferential, sourceZero]

noncomputable def blockDirectRestriction
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectComplex seed (stage + 1) ⟶ blockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexRestriction seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationRestriction seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      exact blockFactorizationDifferential_restriction_square seed stage
    · simp [blockDirectComplex, blockDirectDifferential, sourceZero]

theorem blockDirectRestriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectEulerAction seed (stage + 1) ≫
        blockDirectRestriction seed stage =
      blockDirectRestriction seed stage ≫
        blockDirectEulerAction seed stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (blockWholeVertexRestriction_action_square seed stage) value
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (blockWholeRelationRestriction_action_square seed stage) value
    · let targetSubsingleton : Subsingleton
          ((blockDirectComplex seed stage).X degree) := by
        change Subsingleton (BlockDirectObject seed stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

theorem blockDirectRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectReversal seed (stage + 1) ≫
        blockDirectRestriction seed stage =
      blockDirectRestriction seed stage ≫
        blockDirectReversal seed stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (blockWholeVertexRestriction_reversal_square seed stage) value
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (blockWholeRelationRestriction_reversal_square seed stage) value
    · let targetSubsingleton : Subsingleton
          ((blockDirectComplex seed stage).X degree) := by
        change Subsingleton (BlockDirectObject seed stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

theorem blockDirectEuler_reversal_commutes
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectEulerAction seed stage ≫ blockDirectReversal seed stage =
      blockDirectReversal seed stage ≫ blockDirectEulerAction seed stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexReversal seed stage
        (blockWholeVertexAction seed stage value) =
      blockWholeVertexAction seed stage
        (blockWholeVertexReversal seed stage value)
    exact LinearMap.congr_fun
      (blockWholeVertexAction_reversal_square seed stage).symm value
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationReversal seed stage
          (blockWholeRelationAction seed stage value) =
        blockWholeRelationAction seed stage
          (blockWholeRelationReversal seed stage value)
      exact LinearMap.congr_fun
        (blockWholeRelationAction_reversal_square seed stage).symm value
    · let targetSubsingleton : Subsingleton
          ((blockDirectComplex seed stage).X degree) := by
        change Subsingleton (BlockDirectObject seed stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

theorem blockDirectReversal_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    blockDirectReversal seed stage ≫ blockDirectReversal seed stage =
      𝟙 (blockDirectComplex seed stage) := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexReversal seed stage
        (blockWholeVertexReversal seed stage value) = value
    funext role
    cases role with
    | none => exact blockInnerReversal_involutive seed stage (value none)
    | some row => simp [blockWholeVertexReversal]
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationReversal seed stage
          (blockWholeRelationReversal seed stage value) = value
      funext row
      simp [blockWholeRelationReversal]
    · let targetSubsingleton : Subsingleton
          ((blockDirectComplex seed stage).X degree) := by
        change Subsingleton (BlockDirectObject seed stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

def blockWholeComplexActionOccurrence
    (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (blockDirectComplex seed stage ⟶ blockDirectComplex seed stage)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, blockDirectEulerAction seed stage)

theorem blockWholeComplexActionOccurrence_projects
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeComplexActionOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold blockWholeComplexActionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockWholeComplexActionOccurrence_reads_degree_zero
    (seed : FactorizationPayload) (stage : Nat) :
    ((blockWholeComplexActionOccurrence seed stage).root.2.f 0).hom =
      blockWholeVertexAction seed stage := by
  simp [blockWholeComplexActionOccurrence, blockDirectEulerAction,
    stageOccurrenceFrom]

theorem blockWholeComplexActionOccurrence_reads_degree_one
    (seed : FactorizationPayload) (stage : Nat) :
    ((blockWholeComplexActionOccurrence seed stage).root.2.f 1).hom =
      blockWholeRelationAction seed stage := by
  simp [blockWholeComplexActionOccurrence, blockDirectEulerAction,
    stageOccurrenceFrom]

def blockWholeDeterminantOccurrence
    (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        ((blockDirectComplex seed stage ⟶ blockDirectComplex seed stage) ×
          BlockWholeAlternatingDeterminantAt)) :=
  (blockWholeComplexActionOccurrence seed stage).map fun readout =>
    (readout.1,
      (readout.2, blockWholeAlternatingDeterminant seed stage))

theorem blockWholeDeterminantOccurrence_projects_action
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeDeterminantOccurrence seed stage).map
        (fun readout => (readout.1, readout.2.1)) =
      blockWholeComplexActionOccurrence seed stage := by
  unfold blockWholeDeterminantOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (blockWholeComplexActionOccurrence seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockWholeDeterminantOccurrence_projects_source
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeDeterminantOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold blockWholeDeterminantOccurrence blockWholeComplexActionOccurrence
  rw [RootedAccountedUnfolding.map_map,
    RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockWholeDeterminantOccurrence_reads_alternating_determinant
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeDeterminantOccurrence seed stage).root.2.2 =
      blockWholeAlternatingDeterminant seed stage := by
  simp [blockWholeDeterminantOccurrence,
    blockWholeComplexActionOccurrence, stageOccurrenceFrom]

theorem blockWholeDeterminantOccurrence_cancels_to_inner
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeDeterminantOccurrence seed stage).root.2.2.numerator =
      blockDeterminantSection seed stage *
        (blockWholeDeterminantOccurrence seed stage).root.2.2.denominator := by
  rw [blockWholeDeterminantOccurrence_reads_alternating_determinant]
  exact blockWholeAlternatingDeterminant_cancels_to_inner seed stage

theorem preserves_exact_whole_complex_and_canonical_alternating_determinant
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeDeterminantOccurrence seed stage).map Prod.fst =
        stageOccurrenceFrom seed stage ∧
      ((blockWholeComplexActionOccurrence seed stage).root.2.f 0).hom =
        blockWholeVertexAction seed stage ∧
      ((blockWholeComplexActionOccurrence seed stage).root.2.f 1).hom =
        blockWholeRelationAction seed stage ∧
      (blockWholeDeterminantOccurrence seed stage).root.2.2.numerator =
        blockDeterminantSection seed stage *
          (blockWholeDeterminantOccurrence seed stage).root.2.2.denominator := by
  exact ⟨blockWholeDeterminantOccurrence_projects_source seed stage,
    blockWholeComplexActionOccurrence_reads_degree_zero seed stage,
    blockWholeComplexActionOccurrence_reads_degree_one seed stage,
    blockWholeDeterminantOccurrence_cancels_to_inner seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
