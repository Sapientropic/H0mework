import H0mework.Realization.MappingCone.Functoriality
import H0mework.Arithmetic.EulerGlobal.SolutionAction
import H0mework.Arithmetic.EulerGlobal.WholeHistory

/-!
# Full-Euler action on the common whole factorization relation complex

The persistent whole and every actual quotient-history row are now valued in
the existing integral full-Euler carrier.  The factorization differential is

`d(v)(p,k) = v.whole - p^k * v.quotient(p,k)`.

The same actual Euler action and reversal act pointwise on the vertex and
relation modules, so both commute with `d`.  The source successor applies the
existing Euler-carrier restriction and forgets only newly generated rows.
Thus the full two-term relation complex, its action, reversal, and successor
all arise on one exact factorization occurrence.

This file does not choose a zero-fibre point or assert determinant
cancellation; it supplies the actual derived-action mouth for the frozen
determinant engine.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CochainMappingCoconeFunctoriality
open CategoryTheory
open DerivedAdicCofiber

noncomputable section

abbrev InnerCarrier (seed : FactorizationPayload) (stage : Nat) :=
  CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.Carrier seed stage

abbrev WholeVertexModule (seed : FactorizationPayload) (stage : Nat) :=
  WholeRole seed stage → InnerCarrier seed stage

abbrev WholeRelationModule (seed : FactorizationPayload) (stage : Nat) :=
  FactorRow seed stage → InnerCarrier seed stage

def wholeValue {seed : FactorizationPayload} {stage : Nat}
    (value : WholeVertexModule seed stage) : InnerCarrier seed stage :=
  value none

def quotientValue {seed : FactorizationPayload} {stage : Nat}
    (value : WholeVertexModule seed stage) (row : FactorRow seed stage) :
    InnerCarrier seed stage :=
  value (some row)

/-- Anti-invariant projection of the actual Euler carrier. -/
def innerAntiInvariant (seed : FactorizationPayload) (stage : Nat) :
    InnerCarrier seed stage →ₗ[ℤ] InnerCarrier seed stage :=
  LinearMap.id -
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
      seed stage

/-- Actual whole factorization equation.  Only the anti-invariant whole and
quotient components enter the row. -/
def factorizationDifferential (seed : FactorizationPayload) (stage : Nat) :
    WholeVertexModule seed stage →ₗ[ℤ] WholeRelationModule seed stage where
  toFun := fun value row =>
    innerAntiInvariant seed stage (wholeValue value) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage (quotientValue value row)
  map_add' := by
    intro left right
    funext row
    change innerAntiInvariant seed stage (left none + right none) -
        _ • innerAntiInvariant seed stage
          (left (some row) + right (some row)) =
      (innerAntiInvariant seed stage (left none) -
          _ • innerAntiInvariant seed stage (left (some row))) +
        (innerAntiInvariant seed stage (right none) -
          _ • innerAntiInvariant seed stage (right (some row)))
    rw [map_add, map_add]
    module
  map_smul' := by
    intro scalar value
    funext row
    change innerAntiInvariant seed stage (scalar • value none) -
        _ • innerAntiInvariant seed stage (scalar • value (some row)) =
      scalar • (innerAntiInvariant seed stage (value none) -
        _ • innerAntiInvariant seed stage (value (some row)))
    rw [map_smul, map_smul]
    module

def vertexEulerAction (seed : FactorizationPayload) (stage : Nat) :
    WholeVertexModule seed stage →ₗ[ℤ] WholeVertexModule seed stage where
  toFun := fun value role => carrierEulerAction seed stage (value role)
  map_add' := by
    intro left right
    funext role
    exact (carrierEulerAction seed stage).map_add _ _
  map_smul' := by
    intro scalar value
    funext role
    exact (carrierEulerAction seed stage).map_smul scalar (value role)

def relationEulerAction (seed : FactorizationPayload) (stage : Nat) :
    WholeRelationModule seed stage →ₗ[ℤ] WholeRelationModule seed stage where
  toFun := fun value row => carrierEulerAction seed stage (value row)
  map_add' := by
    intro left right
    funext row
    exact (carrierEulerAction seed stage).map_add _ _
  map_smul' := by
    intro scalar value
    funext row
    change carrierEulerAction seed stage (scalar • value row) =
      scalar • carrierEulerAction seed stage (value row)
    rw [map_smul]

theorem innerAntiInvariant_euler_square
    (seed : FactorizationPayload) (stage : Nat) :
    (innerAntiInvariant seed stage).comp (carrierEulerAction seed stage) =
      (carrierEulerAction seed stage).comp (innerAntiInvariant seed stage) := by
  unfold innerAntiInvariant
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id,
    carrierEuler_reversal_commutes]

theorem innerAntiInvariant_euler
    (seed : FactorizationPayload) (stage : Nat)
    (value : InnerCarrier seed stage) :
    innerAntiInvariant seed stage (carrierEulerAction seed stage value) =
      carrierEulerAction seed stage (innerAntiInvariant seed stage value) :=
  LinearMap.congr_fun (innerAntiInvariant_euler_square seed stage) value

theorem factorizationDifferential_euler_square
    (seed : FactorizationPayload) (stage : Nat) :
    (factorizationDifferential seed stage).comp
        (vertexEulerAction seed stage) =
      (relationEulerAction seed stage).comp
        (factorizationDifferential seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change innerAntiInvariant seed stage
        (carrierEulerAction seed stage (wholeValue value)) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage
          (carrierEulerAction seed stage (quotientValue value row)) =
    carrierEulerAction seed stage
      (innerAntiInvariant seed stage (wholeValue value) -
        (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
          innerAntiInvariant seed stage (quotientValue value row))
  rw [innerAntiInvariant_euler, innerAntiInvariant_euler,
    map_sub, map_smul]

def vertexReversal (seed : FactorizationPayload) (stage : Nat) :
    WholeVertexModule seed stage →ₗ[ℤ] WholeVertexModule seed stage where
  toFun := fun value role =>
    match role with
    | none =>
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
          seed stage (value none)
    | some row => -value (some row)
  map_add' := by
    intro left right
    funext role
    cases role with
    | none =>
        exact (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
          seed stage).map_add _ _
    | some row =>
        change -(left (some row) + right (some row)) =
          -left (some row) + -right (some row)
        module
  map_smul' := by
    intro scalar value
    funext role
    cases role with
    | none =>
        exact (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
          seed stage).map_smul scalar (value none)
    | some row =>
        change -(scalar • value (some row)) = scalar • (-value (some row))
        module

def relationReversal (seed : FactorizationPayload) (stage : Nat) :
    WholeRelationModule seed stage →ₗ[ℤ] WholeRelationModule seed stage where
  toFun := fun value row => -value row
  map_add' := by
    intro left right
    funext row
    change -(left row + right row) = -left row + -right row
    module
  map_smul' := by
    intro scalar value
    funext row
    change -(scalar • value row) = scalar • (-value row)
    module

theorem innerAntiInvariant_reversal
    (seed : FactorizationPayload) (stage : Nat)
    (value : InnerCarrier seed stage) :
    innerAntiInvariant seed stage
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
          seed stage value) =
      -innerAntiInvariant seed stage value := by
  unfold innerAntiInvariant
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  rw [CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal_involutive]
  module

theorem factorizationDifferential_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (factorizationDifferential seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
          seed stage) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
        seed stage).comp
        (factorizationDifferential seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change innerAntiInvariant seed stage
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
          seed stage (wholeValue value)) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage (-(quotientValue value row)) =
    -(innerAntiInvariant seed stage (wholeValue value) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage (quotientValue value row))
  rw [innerAntiInvariant_reversal, map_neg]
  module

theorem vertexEuler_reversal_commutes (seed : FactorizationPayload)
    (stage : Nat) :
    (vertexEulerAction seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
          seed stage) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
        seed stage).comp (vertexEulerAction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun (carrierEuler_reversal_commutes seed stage)
        (value none)
  | some row =>
      change carrierEulerAction seed stage (-value (some row)) =
        -carrierEulerAction seed stage (value (some row))
      rw [map_neg]

theorem relationEuler_reversal_commutes (seed : FactorizationPayload)
    (stage : Nat) :
    (relationEulerAction seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
          seed stage) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
        seed stage).comp (relationEulerAction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change carrierEulerAction seed stage (-value row) =
    -carrierEulerAction seed stage (value row)
  rw [map_neg]

def vertexRestriction (seed : FactorizationPayload) (stage : Nat) :
    WholeVertexModule seed (stage + 1) →ₗ[ℤ]
      WholeVertexModule seed stage where
  toFun := fun value role =>
    match role with
    | none =>
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage (value none)
    | some row =>
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage
        (value (some (liftFactorRow seed stage row)))
  map_add' := by
    intro left right
    funext role
    cases role <;> simp only [Pi.add_apply, map_add]
  map_smul' := by
    intro scalar value
    funext role
    cases role <;> simp only [Pi.smul_apply] <;>
      exact (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage).map_smul scalar _

def relationRestriction (seed : FactorizationPayload) (stage : Nat) :
    WholeRelationModule seed (stage + 1) →ₗ[ℤ]
      WholeRelationModule seed stage where
  toFun := fun value row =>
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
      seed stage (value (liftFactorRow seed stage row))
  map_add' := by
    intro left right
    funext row
    exact (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
      seed stage).map_add _ _
  map_smul' := by
    intro scalar value
    funext row
    change
      CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage (scalar • value (liftFactorRow seed stage row)) =
        scalar •
          CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage (value (liftFactorRow seed stage row))
    rw [map_smul]

theorem carrierRestriction_innerAntiInvariant_square
    (seed : FactorizationPayload) (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage).comp (innerAntiInvariant seed (stage + 1)) =
      (innerAntiInvariant seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage) := by
  unfold innerAntiInvariant
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction_reversal_square]

theorem innerAntiInvariant_restriction
    (seed : FactorizationPayload) (stage : Nat)
    (value : InnerCarrier seed (stage + 1)) :
    innerAntiInvariant seed stage
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage value) =
      CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage (innerAntiInvariant seed (stage + 1) value) :=
  (LinearMap.congr_fun
    (carrierRestriction_innerAntiInvariant_square seed stage) value).symm

theorem factorizationRestriction_differential_square
    (seed : FactorizationPayload) (stage : Nat) :
    (factorizationDifferential seed stage).comp
        (vertexRestriction seed stage) =
      (relationRestriction seed stage).comp
        (factorizationDifferential seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext row
  change innerAntiInvariant seed stage
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage (value none)) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage
          (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage (value (some (liftFactorRow seed stage row)))) =
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
      seed stage
      (innerAntiInvariant seed (stage + 1) (value none) -
        (((rowPrime (liftFactorRow seed stage row) : Nat) : ℤ) ^
            rowExponent (liftFactorRow seed stage row)) •
          innerAntiInvariant seed (stage + 1)
            (value (some (liftFactorRow seed stage row))))
  rw [innerAntiInvariant_restriction, innerAntiInvariant_restriction,
    liftFactorRow_prime, liftFactorRow_exponent, map_sub, map_smul]

theorem vertexRestriction_euler_square (seed : FactorizationPayload)
    (stage : Nat) :
    (vertexRestriction seed stage).comp
        (vertexEulerAction seed (stage + 1)) =
      (vertexEulerAction seed stage).comp
        (vertexRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (carrierRestriction_euler_square seed stage) (value none)
  | some row =>
      exact LinearMap.congr_fun
        (carrierRestriction_euler_square seed stage)
          (value (some (liftFactorRow seed stage row)))

theorem relationRestriction_euler_square (seed : FactorizationPayload)
    (stage : Nat) :
    (relationRestriction seed stage).comp
        (relationEulerAction seed (stage + 1)) =
      (relationEulerAction seed stage).comp
        (relationRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun (carrierRestriction_euler_square seed stage)
    (value (liftFactorRow seed stage row))

theorem vertexRestriction_reversal_square (seed : FactorizationPayload)
    (stage : Nat) :
    (vertexRestriction seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
          seed (stage + 1)) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
        seed stage).comp (vertexRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction_reversal_square
          seed stage) (value none)
  | some row =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage (-value (some (liftFactorRow seed stage row))) =
          -CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage (value (some (liftFactorRow seed stage row)))
      rw [map_neg]

theorem relationRestriction_reversal_square (seed : FactorizationPayload)
    (stage : Nat) :
    (relationRestriction seed stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
          seed (stage + 1)) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
        seed stage).comp (relationRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage (-value (liftFactorRow seed stage row)) =
      -CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage (value (liftFactorRow seed stage row))
  rw [map_neg]

noncomputable abbrev VertexObject (seed : FactorizationPayload) (stage : Nat) :=
  ModuleCat.of ℤ (WholeVertexModule seed stage)

noncomputable abbrev RelationObject (seed : FactorizationPayload) (stage : Nat) :=
  ModuleCat.of ℤ (WholeRelationModule seed stage)

noncomputable abbrev vertexComplex (seed : FactorizationPayload) (stage : Nat) :
    IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (VertexObject seed stage)

noncomputable abbrev relationComplex (seed : FactorizationPayload)
    (stage : Nat) : IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (RelationObject seed stage)

noncomputable def differentialMap (seed : FactorizationPayload) (stage : Nat) :
    vertexComplex seed stage ⟶ relationComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (factorizationDifferential seed stage))

noncomputable abbrev wholeRelationComplex (seed : FactorizationPayload)
    (stage : Nat) : IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone (differentialMap seed stage)

noncomputable def vertexEulerMap (seed : FactorizationPayload) (stage : Nat) :
    vertexComplex seed stage ⟶ vertexComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (vertexEulerAction seed stage))

noncomputable def relationEulerMap (seed : FactorizationPayload) (stage : Nat) :
    relationComplex seed stage ⟶ relationComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (relationEulerAction seed stage))

theorem eulerMap_differential_square (seed : FactorizationPayload)
    (stage : Nat) :
    vertexEulerMap seed stage ≫ differentialMap seed stage =
      differentialMap seed stage ≫ relationEulerMap seed stage := by
  unfold vertexEulerMap differentialMap relationEulerMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact factorizationDifferential_euler_square seed stage

noncomputable def wholeEulerAction (seed : FactorizationPayload) (stage : Nat) :
    wholeRelationComplex seed stage ⟶ wholeRelationComplex seed stage :=
  mappingCoconeMap (differentialMap seed stage) (differentialMap seed stage)
    (vertexEulerMap seed stage) (relationEulerMap seed stage)
      (eulerMap_differential_square seed stage)

noncomputable def vertexReversalMap (seed : FactorizationPayload) (stage : Nat) :
    vertexComplex seed stage ⟶ vertexComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
        seed stage))

noncomputable def relationReversalMap (seed : FactorizationPayload)
    (stage : Nat) : relationComplex seed stage ⟶ relationComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
        seed stage))

theorem reversalMap_differential_square (seed : FactorizationPayload)
    (stage : Nat) :
    vertexReversalMap seed stage ≫ differentialMap seed stage =
      differentialMap seed stage ≫ relationReversalMap seed stage := by
  unfold vertexReversalMap differentialMap relationReversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact factorizationDifferential_reversal_square seed stage

noncomputable def wholeReversal (seed : FactorizationPayload) (stage : Nat) :
    wholeRelationComplex seed stage ⟶ wholeRelationComplex seed stage :=
  mappingCoconeMap (differentialMap seed stage) (differentialMap seed stage)
    (vertexReversalMap seed stage) (relationReversalMap seed stage)
      (reversalMap_differential_square seed stage)

noncomputable def vertexRestrictionMap (seed : FactorizationPayload)
    (stage : Nat) : vertexComplex seed (stage + 1) ⟶ vertexComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (vertexRestriction seed stage))

noncomputable def relationRestrictionMap (seed : FactorizationPayload)
    (stage : Nat) :
    relationComplex seed (stage + 1) ⟶ relationComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (relationRestriction seed stage))

theorem restrictionMap_differential_square (seed : FactorizationPayload)
    (stage : Nat) :
    vertexRestrictionMap seed stage ≫ differentialMap seed stage =
      differentialMap seed (stage + 1) ≫ relationRestrictionMap seed stage := by
  unfold vertexRestrictionMap differentialMap relationRestrictionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact factorizationRestriction_differential_square seed stage

noncomputable def wholeRelationTransition (seed : FactorizationPayload)
    (stage : Nat) :
    wholeRelationComplex seed (stage + 1) ⟶
      wholeRelationComplex seed stage :=
  mappingCoconeMap (differentialMap seed (stage + 1))
    (differentialMap seed stage) (vertexRestrictionMap seed stage)
      (relationRestrictionMap seed stage)
        (restrictionMap_differential_square seed stage)

def actionOccurrence (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (wholeRelationComplex seed stage ⟶ wholeRelationComplex seed stage)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, wholeEulerAction seed stage)

theorem actionOccurrence_projects (seed : FactorizationPayload)
    (stage : Nat) :
    (actionOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold actionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_factorization_action_reversal_and_successor
    (seed : FactorizationPayload) (stage : Nat) :
    (actionOccurrence seed stage).root.2 = wholeEulerAction seed stage ∧
      (factorizationDifferential seed stage).comp
          (vertexEulerAction seed stage) =
        (relationEulerAction seed stage).comp
          (factorizationDifferential seed stage) ∧
      (factorizationDifferential seed stage).comp
          (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
            seed stage) =
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
          seed stage).comp
          (factorizationDifferential seed stage) ∧
      (factorizationDifferential seed stage).comp
          (vertexRestriction seed stage) =
        (relationRestriction seed stage).comp
          (factorizationDifferential seed (stage + 1)) := by
  exact ⟨by simp [actionOccurrence],
    factorizationDifferential_euler_square seed stage,
    factorizationDifferential_reversal_square seed stage,
    factorizationRestriction_differential_square seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
