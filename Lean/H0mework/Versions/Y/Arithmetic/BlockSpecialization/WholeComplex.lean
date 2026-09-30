import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.Stage
import H0mework.Versions.Y.Arithmetic.EulerDualBlock.WholeRelationDeterminant
import H0mework.Versions.X.Arithmetic.EulerGlobal.WholeDerivedSection

/-!
# Arithmetic specialization of the complete block whole/relation complex

The coefficientwise arithmetic read is applied to every whole and relation
role.  It commutes with the actual factorization differential, Euler action,
reversal, and runtime successor.  After forgetting only the block-ring scalar
structure, this gives a genuine chain map to the existing integral direct
whole/relation complex.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace BlockArithmeticSpecializationWholeComplex

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open BlockArithmeticSpecializationStage
open CategoryTheory
open DerivedAdicCofiber

noncomputable section

def blockWholeVertexRead (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[ℤ] WholeVertexModule seed stage where
  toFun := fun value role => blockInnerCarrierRead seed stage (value role)
  map_add' := by
    intro left right
    funext role
    exact (blockInnerCarrierRead seed stage).map_add _ _
  map_smul' := by
    intro scalar value
    funext role
    exact (blockInnerCarrierRead seed stage).map_smul scalar (value role)

def blockWholeRelationRead (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed stage →ₗ[ℤ]
      WholeRelationModule seed stage where
  toFun := fun value row => blockInnerCarrierRead seed stage (value row)
  map_add' := by
    intro left right
    funext row
    exact (blockInnerCarrierRead seed stage).map_add _ _
  map_smul' := by
    intro scalar value
    funext row
    exact (blockInnerCarrierRead seed stage).map_smul scalar (value row)

theorem blockInnerCarrierRead_antiInvariant
    (seed : FactorizationPayload) (stage : Nat)
    (value : BlockInner seed stage) :
    blockInnerCarrierRead seed stage
        (blockInnerAntiInvariant seed stage value) =
      innerAntiInvariant seed stage
        (blockInnerCarrierRead seed stage value) := by
  unfold blockInnerAntiInvariant innerAntiInvariant
  rw [LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  exact congrArg (fun reversed =>
      blockInnerCarrierRead seed stage value - reversed)
    (LinearMap.congr_fun
      (blockInnerCarrierRead_reversal_square seed stage) value)

theorem blockFactorizationDifferential_specialization_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRead seed stage).comp
        ((blockFactorizationDifferential seed stage).restrictScalars ℤ) =
      (factorizationDifferential seed stage).comp
        (blockWholeVertexRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change blockInnerCarrierRead seed stage
      (blockInnerAntiInvariant seed stage (value none) -
        (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
          blockInnerAntiInvariant seed stage (value (some row))) =
    innerAntiInvariant seed stage
        (blockInnerCarrierRead seed stage (value none)) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage
          (blockInnerCarrierRead seed stage (value (some row)))
  rw [map_sub, blockInnerCarrierRead_block_smul,
    blockInnerCarrierRead_antiInvariant,
    blockInnerCarrierRead_antiInvariant]
  simp

theorem blockWholeVertexRead_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexRead seed stage).comp
        ((blockWholeVertexAction seed stage).restrictScalars ℤ) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexEulerAction
          seed stage).comp
        (blockWholeVertexRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  exact LinearMap.congr_fun
    (blockInnerCarrierRead_action_square seed stage) (value role)

theorem blockWholeRelationRead_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRead seed stage).comp
        ((blockWholeRelationAction seed stage).restrictScalars ℤ) =
      (relationEulerAction seed stage).comp
        (blockWholeRelationRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun
    (blockInnerCarrierRead_action_square seed stage) (value row)

theorem blockWholeVertexRead_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexRead seed stage).comp
        ((blockWholeVertexReversal seed stage).restrictScalars ℤ) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
          seed stage).comp (blockWholeVertexRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerCarrierRead_reversal_square seed stage) (value none)
  | some row =>
      change blockInnerCarrierRead seed stage (-value (some row)) =
        -blockInnerCarrierRead seed stage (value (some row))
      rw [map_neg]

theorem blockWholeRelationRead_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRead seed stage).comp
        ((blockWholeRelationReversal seed stage).restrictScalars ℤ) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
          seed stage).comp (blockWholeRelationRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change blockInnerCarrierRead seed stage (-value row) =
    -blockInnerCarrierRead seed stage (value row)
  rw [map_neg]

theorem blockWholeVertexRead_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexRead seed stage).comp
        ((blockWholeVertexRestriction seed stage).restrictScalars ℤ) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
          seed stage).comp (blockWholeVertexRead seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerCarrierRead_restriction_square seed stage) (value none)
  | some row =>
      exact LinearMap.congr_fun
        (blockInnerCarrierRead_restriction_square seed stage)
          (value (some (liftFactorRow seed stage row)))

theorem blockWholeRelationRead_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRead seed stage).comp
        ((blockWholeRelationRestriction seed stage).restrictScalars ℤ) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
          seed stage).comp
        (blockWholeRelationRead seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun
    (blockInnerCarrierRead_restriction_square seed stage)
      (value (liftFactorRow seed stage row))

/-- The universal block complex regarded as an integral additive complex.
This is degreewise restriction along `ℤ → BlockCoordinateRing`; it makes no
claim that extension of scalars commutes with an inverse limit. -/
abbrev ArithmeticBlockZeroCarrier := Fin 0 → BlockCoordinateRing

noncomputable abbrev ArithmeticBlockDirectObject
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    ModuleCat ℤ :=
  if degree = 0 then ModuleCat.of ℤ (BlockWholeVertex seed stage)
  else if degree = 1 then ModuleCat.of ℤ (BlockWholeRelation seed stage)
  else ModuleCat.of ℤ ArithmeticBlockZeroCarrier

noncomputable def arithmeticBlockDirectDifferential
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    ArithmeticBlockDirectObject seed stage degree ⟶
      ArithmeticBlockDirectObject seed stage (degree + 1) := by
  by_cases degreeZero : degree = 0
  · subst degree
    exact ModuleCat.ofHom
      ((blockFactorizationDifferential seed stage).restrictScalars ℤ)
  · exact 0

theorem arithmeticBlockDirectDifferential_sq
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    arithmeticBlockDirectDifferential seed stage degree ≫
        arithmeticBlockDirectDifferential seed stage (degree + 1) = 0 := by
  by_cases degreeZero : degree = 0
  · subst degree
    simp [arithmeticBlockDirectDifferential]
  · simp [arithmeticBlockDirectDifferential, degreeZero]

noncomputable abbrev UnderlyingBlockDirectComplex
    (seed : FactorizationPayload) (stage : Nat) :
    IntegralCochainComplex ℤ :=
  CochainComplex.of (ArithmeticBlockDirectObject seed stage)
    (arithmeticBlockDirectDifferential seed stage)
    (arithmeticBlockDirectDifferential_sq seed stage)

/-- Chain-level arithmetic read from the complete universal block complex to
the existing integral direct whole/relation complex. -/
noncomputable def blockDirectIntegralRead
    (seed : FactorizationPayload) (stage : Nat) :
    UnderlyingBlockDirectComplex seed stage ⟶ directComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexRead seed stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationRead seed stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      change ModuleCat.ofHom (blockWholeVertexRead seed stage) ≫
          ModuleCat.ofHom (factorizationDifferential seed stage) =
        ModuleCat.ofHom
            ((blockFactorizationDifferential seed stage).restrictScalars ℤ) ≫
          ModuleCat.ofHom (blockWholeRelationRead seed stage)
      apply ModuleCat.hom_ext
      exact (blockFactorizationDifferential_specialization_square
        seed stage).symm
    · simp [UnderlyingBlockDirectComplex, arithmeticBlockDirectDifferential,
        directComplex,
        directDifferential, sourceZero]

def blockDirectIntegralReadOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (UnderlyingBlockDirectComplex seedOccurrence.root stage ⟶
          directComplex seedOccurrence.root stage)) :=
  (stageOccurrenceFrom seedOccurrence.root stage).map fun owner =>
    (owner, blockDirectIntegralRead seedOccurrence.root stage)

theorem blockDirectIntegralReadOccurrence_projects (stage : Nat) :
    (blockDirectIntegralReadOccurrence stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage := by
  unfold blockDirectIntegralReadOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seedOccurrence.root stage).map id = _
  exact RootedAccountedUnfolding.map_id _

end
end BlockArithmeticSpecializationWholeComplex
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
