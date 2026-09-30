import H0mework.Arithmetic.EulerGlobal.WholeUniversalSolution
import H0mework.Arithmetic.EulerGlobal.HistoryCofinalRigidity

/-!
# Integral whole-history solutions inside the full-Euler relation action

The common whole-history solution is generated over `ℤ` before any
determinant zero-fibre scalar extension.  At every finite runtime occurrence,
an integral whole/quotient solution is sent to the full-Euler relation vertex
by extending each dual pair constantly over the actual prime base and then
using the generated exponent-recurrence solution.

The embedding is a chain map, commutes with the actual source successor and
with reversal, and therefore generates a map between the two frozen global
dependent states.  No rational division root or scalar relation kernel enters
this construction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber

noncomputable section

abbrev IntegralLocalCarrier (seed : FactorizationPayload) (stage : Nat) :=
  CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.Carrier
    seed stage

abbrev EulerLocalCarrier (seed : FactorizationPayload) (stage : Nat) :=
  CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.Carrier
    seed stage

/-- Forget the prime label while retaining the actual dual value. -/
def constantEulerBase (seed : FactorizationPayload) (stage : Nat) :
    DualBase →ₗ[ℤ]
      CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.BaseLattice
        seed stage where
  toFun := fun value index => value index.2
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

/-- The exponent-recurrence fold generated from one integral dual pair. -/
def localInnerEmbedding (seed : FactorizationPayload) (stage : Nat) :
    DualBase →ₗ[ℤ] EulerLocalCarrier seed stage :=
  (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.solutionOfBase
    seed stage).comp (constantEulerBase seed stage)

def dualBaseReversal : DualBase →ₗ[ℤ] DualBase where
  toFun := fun value dualIndex => value dualIndex.rev
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def wholeRoleRead (seed : FactorizationPayload) (stage : Nat) :
    IntegralLocalCarrier seed stage →ₗ[ℤ] DualBase where
  toFun := fun value dualIndex => wholeCoordinate seed stage dualIndex value
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

/-- Integral sign representation `q ↦ (q,0)` before the full-Euler
anti-invariant projection. -/
def quotientBase : ℤ →ₗ[ℤ] DualBase where
  toFun := fun value dualIndex => if dualIndex = 0 then value else 0
  map_add' := by
    intro left right
    funext dualIndex
    split <;> simp_all
  map_smul' := by
    intro scalar value
    funext dualIndex
    split <;> simp_all

def quotientRoleRead (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage) :
    IntegralLocalCarrier seed stage →ₗ[ℤ] DualBase :=
  quotientBase.comp (quotientCoordinate row)

def roleRead (seed : FactorizationPayload) (stage : Nat)
    (role : WholeRole seed stage) :
    IntegralLocalCarrier seed stage →ₗ[ℤ] DualBase :=
  match role with
  | none => wholeRoleRead seed stage
  | some row => quotientRoleRead seed stage row

/-- One common integral solution becomes one vertex of the actual full-Euler
relation complex. -/
def localVertexEmbedding (seed : FactorizationPayload) (stage : Nat) :
    IntegralLocalCarrier seed stage →ₗ[ℤ]
      WholeVertexModule seed stage where
  toFun := fun value role =>
    localInnerEmbedding seed stage (roleRead seed stage role value)
  map_add' := by
    intro left right
    funext role
    change localInnerEmbedding seed stage
        (roleRead seed stage role (left + right)) =
      localInnerEmbedding seed stage (roleRead seed stage role left) +
        localInnerEmbedding seed stage (roleRead seed stage role right)
    rw [map_add, map_add]
  map_smul' := by
    intro scalar value
    funext role
    change localInnerEmbedding seed stage
        (roleRead seed stage role (scalar • value)) =
      scalar • localInnerEmbedding seed stage (roleRead seed stage role value)
    rw [map_smul, map_smul]

theorem roleRead_antiInvariant_eq_primePower_smul_quotient
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage) (value : IntegralLocalCarrier seed stage) :
    roleRead seed stage none value -
        dualBaseReversal (roleRead seed stage none value) =
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        (roleRead seed stage (some row) value -
          dualBaseReversal (roleRead seed stage (some row) value)) := by
  funext dualIndex
  have landing := wholeDifference_eq_primePower_mul_quotientCoordinate
    seed stage row value
  fin_cases dualIndex
  · simpa [roleRead, wholeRoleRead, quotientRoleRead, quotientBase,
      dualBaseReversal, wholeDifference, smul_eq_mul] using landing
  · have reversedLanding := congrArg Neg.neg landing
    simpa [roleRead, wholeRoleRead, quotientRoleRead, quotientBase,
      dualBaseReversal, wholeDifference, smul_eq_mul] using reversedLanding

theorem localInnerEmbedding_reversal
    (seed : FactorizationPayload) (stage : Nat) (value : DualBase) :
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
        seed stage (localInnerEmbedding seed stage value) =
      localInnerEmbedding seed stage (dualBaseReversal value) := by
  apply Subtype.ext
  funext index
  rfl

theorem innerAntiInvariant_localInnerEmbedding
    (seed : FactorizationPayload) (stage : Nat) (value : DualBase) :
    innerAntiInvariant seed stage (localInnerEmbedding seed stage value) =
      localInnerEmbedding seed stage (value - dualBaseReversal value) := by
  unfold innerAntiInvariant
  rw [LinearMap.sub_apply, LinearMap.id_apply,
    localInnerEmbedding_reversal, map_sub]

theorem roleRead_none_restriction
    (seed : FactorizationPayload) (stage : Nat)
    (value : IntegralLocalCarrier seed (stage + 1)) :
    roleRead seed (stage + 1) none value =
      roleRead seed stage none
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction
          seed stage value) := by
  funext dualIndex
  rfl

theorem roleRead_some_restriction
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage)
    (value : IntegralLocalCarrier seed (stage + 1)) :
    roleRead seed (stage + 1) (some (liftFactorRow seed stage row)) value =
      roleRead seed stage (some row)
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction
          seed stage value) := by
  funext dualIndex
  fin_cases dualIndex <;> rfl

theorem roleRead_none_reversal
    (seed : FactorizationPayload) (stage : Nat)
    (value : IntegralLocalCarrier seed stage) :
    roleRead seed stage none
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
          seed stage value) =
      dualBaseReversal (roleRead seed stage none value) := by
  funext dualIndex
  rfl

theorem roleRead_some_reversal
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage)
    (value : IntegralLocalCarrier seed stage) :
    roleRead seed stage (some row)
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
          seed stage value) =
      -roleRead seed stage (some row) value := by
  funext dualIndex
  fin_cases dualIndex <;> rfl

/-- The embedding lands in the cocycle kernel because it consumes the actual
integral factorization equations before scalar extension. -/
theorem factorizationDifferential_localVertexEmbedding_eq_zero
    (seed : FactorizationPayload) (stage : Nat)
    (value : IntegralLocalCarrier seed stage) :
    factorizationDifferential seed stage
        (localVertexEmbedding seed stage value) = 0 := by
  funext row
  change innerAntiInvariant seed stage
        (localInnerEmbedding seed stage (roleRead seed stage none value)) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seed stage
          (localInnerEmbedding seed stage
            (roleRead seed stage (some row) value)) = 0
  rw [innerAntiInvariant_localInnerEmbedding,
    innerAntiInvariant_localInnerEmbedding, ← map_smul, ← map_sub,
    roleRead_antiInvariant_eq_primePower_smul_quotient,
    sub_self, map_zero]

theorem carrierRestriction_localInnerEmbedding
    (seed : FactorizationPayload) (stage : Nat) (value : DualBase) :
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seed stage (localInnerEmbedding seed (stage + 1) value) =
      localInnerEmbedding seed stage value := by
  apply (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierEquivBase
    seed stage).injective
  change
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead seed stage
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seed stage (localInnerEmbedding seed (stage + 1) value)) =
      CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead seed stage
        (localInnerEmbedding seed stage value)
  rw [CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead_carrierRestriction]
  simp only [localInnerEmbedding, LinearMap.comp_apply,
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead_solutionOfBase]
  funext index
  rfl

theorem localVertexEmbedding_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
      seed stage).comp
        (localVertexEmbedding seed (stage + 1)) =
      (localVertexEmbedding seed stage).comp
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction
          seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage
            (localInnerEmbedding seed (stage + 1)
              (roleRead seed (stage + 1) none value)) =
          localInnerEmbedding seed stage
            (roleRead seed stage none
              (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction
                seed stage value))
      rw [carrierRestriction_localInnerEmbedding]
      exact congrArg (localInnerEmbedding seed stage)
        (roleRead_none_restriction seed stage value)
  | some row =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seed stage
            (localInnerEmbedding seed (stage + 1)
              (roleRead seed (stage + 1) (some (liftFactorRow seed stage row))
                value)) =
          localInnerEmbedding seed stage
            (roleRead seed stage (some row)
              (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction
                seed stage value))
      rw [carrierRestriction_localInnerEmbedding]
      exact congrArg (localInnerEmbedding seed stage)
        (roleRead_some_restriction seed stage row value)

theorem localVertexEmbedding_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
      seed stage).comp (localVertexEmbedding seed stage) =
      (localVertexEmbedding seed stage).comp
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
          seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
            seed stage
            (localInnerEmbedding seed stage (roleRead seed stage none value)) =
          localInnerEmbedding seed stage
            (roleRead seed stage none
              (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
                seed stage value))
      rw [localInnerEmbedding_reversal, roleRead_none_reversal]
  | some row =>
      change
        -(localInnerEmbedding seed stage
            (roleRead seed stage (some row) value)) =
          localInnerEmbedding seed stage
            (roleRead seed stage (some row)
              (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
                seed stage value))
      rw [roleRead_some_reversal, map_neg]

/-- Chain-level integral-first inclusion at one actual occurrence. -/
noncomputable def localComplexEmbedding
    (seed : FactorizationPayload) (stage : Nat) :
    ActualComplex seed stage ⟶ directComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (localVertexEmbedding seed stage)
    · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      change ModuleCat.ofHom (localVertexEmbedding seed stage) ≫
          ModuleCat.ofHom (factorizationDifferential seed stage) = 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact factorizationDifferential_localVertexEmbedding_eq_zero seed stage
    · simp [ActualComplex, directComplex, directDifferential, sourceZero]

noncomputable def localIntegralReversal
    (seed : FactorizationPayload) (stage : Nat) :
    ActualComplex seed stage ⟶ ActualComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal
          seed stage)
    · exact 0
  comm' _source _target _related := by
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [comp_zero, zero_comp]

theorem localComplexEmbedding_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    localIntegralReversal seed stage ≫ localComplexEmbedding seed stage =
      localComplexEmbedding seed stage ≫ directReversal seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (localVertexEmbedding_reversal_square seed stage).symm _
  · simp [localIntegralReversal, localComplexEmbedding, directReversal,
      degreeZero]

theorem localComplexEmbedding_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    actualRestriction seed stage ≫ localComplexEmbedding seed stage =
      localComplexEmbedding seed (stage + 1) ≫ directRestriction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (localVertexEmbedding_restriction_square seed stage).symm _
  · simp [actualRestriction, localComplexEmbedding, directRestriction,
      degreeZero]

theorem localIntegralReversal_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    localIntegralReversal seed (stage + 1) ≫ actualRestriction seed stage =
      actualRestriction seed stage ≫ localIntegralReversal seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierRestriction_reversal_square
        seed stage) _
  · simp [localIntegralReversal, actualRestriction, degreeZero]

noncomputable def embeddingNatTrans (seed : FactorizationPayload) :
    solutionDiagram seed ⟶ localRelationDiagram seed :=
  NatTrans.ofOpSequence
    (localComplexEmbedding seed)
    (fun stage => by
      simp only [solutionDiagram, localRelationDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact localComplexEmbedding_restriction_square seed stage)

noncomputable def integralReversalNatTrans (seed : FactorizationPayload) :
    solutionDiagram seed ⟶ solutionDiagram seed :=
  NatTrans.ofOpSequence
    (localIntegralReversal seed)
    (fun stage => by
      simp only [solutionDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      exact (localIntegralReversal_restriction_square seed stage).symm)

noncomputable def globalIntegralEmbedding :
    limit (solutionDiagram seedOccurrence.root) ⟶
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.GlobalState := by
  change limit (solutionDiagram seedOccurrence.root) ⟶
    limit (localRelationDiagram seedOccurrence.root)
  exact limMap (embeddingNatTrans seedOccurrence.root)

noncomputable def globalIntegralReversal :
    limit (solutionDiagram seedOccurrence.root) ⟶
      limit (solutionDiagram seedOccurrence.root) := by
  exact limMap (integralReversalNatTrans seedOccurrence.root)

def integralGlobalInclusion :
    ((limit (solutionDiagram seedOccurrence.root)).X 0 : Type) →ₗ[ℤ]
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution.GlobalVertex :=
  (globalIntegralEmbedding.f 0).hom

def integralGlobalReversalLinear :
    ((limit (solutionDiagram seedOccurrence.root)).X 0 : Type) →ₗ[ℤ]
      ((limit (solutionDiagram seedOccurrence.root)).X 0 : Type) :=
  (globalIntegralReversal.f 0).hom

theorem globalIntegralEmbedding_reversal_square :
    globalIntegralReversal ≫ globalIntegralEmbedding =
      globalIntegralEmbedding ≫
        CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalReversal := by
  change
    limMap (integralReversalNatTrans seedOccurrence.root) ≫
        limMap (embeddingNatTrans seedOccurrence.root) =
      limMap (embeddingNatTrans seedOccurrence.root) ≫
        limMap (reversalNatTrans seedOccurrence.root)
  apply limit.hom_ext
  intro stage
  calc
    (limMap (integralReversalNatTrans seedOccurrence.root) ≫
        limMap (embeddingNatTrans seedOccurrence.root)) ≫
        limit.π (localRelationDiagram seedOccurrence.root) stage =
      (limMap (integralReversalNatTrans seedOccurrence.root) ≫
        limit.π (solutionDiagram seedOccurrence.root) stage) ≫
        (embeddingNatTrans seedOccurrence.root).app stage := by
          rw [Category.assoc, limMap_π, ← Category.assoc]
    _ = (limit.π (solutionDiagram seedOccurrence.root) stage ≫
        (integralReversalNatTrans seedOccurrence.root).app stage) ≫
        (embeddingNatTrans seedOccurrence.root).app stage := by
          rw [limMap_π]
    _ = limit.π (solutionDiagram seedOccurrence.root) stage ≫
        ((embeddingNatTrans seedOccurrence.root).app stage ≫
          (reversalNatTrans seedOccurrence.root).app stage) := by
          rw [Category.assoc]
          congr 1
          exact localComplexEmbedding_reversal_square
            seedOccurrence.root stage.unop
    _ = (limMap (embeddingNatTrans seedOccurrence.root) ≫
        limMap (reversalNatTrans seedOccurrence.root)) ≫
          limit.π (localRelationDiagram seedOccurrence.root) stage := by
          symm
          calc
            (limMap (embeddingNatTrans seedOccurrence.root) ≫
                limMap (reversalNatTrans seedOccurrence.root)) ≫
                limit.π (localRelationDiagram seedOccurrence.root) stage =
              limMap (embeddingNatTrans seedOccurrence.root) ≫
                (limMap (reversalNatTrans seedOccurrence.root) ≫
                  limit.π (localRelationDiagram seedOccurrence.root) stage) :=
                    Category.assoc _ _ _
            _ = limMap (embeddingNatTrans seedOccurrence.root) ≫
                (limit.π (localRelationDiagram seedOccurrence.root) stage ≫
                  (reversalNatTrans seedOccurrence.root).app stage) := by
                    rw [limMap_π]
            _ = (limMap (embeddingNatTrans seedOccurrence.root) ≫
                limit.π (localRelationDiagram seedOccurrence.root) stage) ≫
                  (reversalNatTrans seedOccurrence.root).app stage :=
                    (Category.assoc _ _ _).symm
            _ = (limit.π (solutionDiagram seedOccurrence.root) stage ≫
                (embeddingNatTrans seedOccurrence.root).app stage) ≫
                  (reversalNatTrans seedOccurrence.root).app stage := by
                    rw [limMap_π]

theorem integralGlobalInclusion_reversal_square :
    integralGlobalInclusion.comp integralGlobalReversalLinear =
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution.globalReversalZero.comp
        integralGlobalInclusion := by
  exact congrArg
    (fun arrow :
      limit (solutionDiagram seedOccurrence.root) ⟶
        CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.GlobalState =>
      (arrow.f 0).hom)
    globalIntegralEmbedding_reversal_square

theorem globalIntegralReversal_involutive :
    Function.Involutive integralGlobalReversalLinear := by
  intro value
  have localInvolutive (stage : ℕᵒᵖ) :
      (integralReversalNatTrans seedOccurrence.root).app stage ≫
          (integralReversalNatTrans seedOccurrence.root).app stage =
        𝟙 ((solutionDiagram seedOccurrence.root).obj stage) := by
    change localIntegralReversal seedOccurrence.root stage.unop ≫
        localIntegralReversal seedOccurrence.root stage.unop =
      𝟙 (ActualComplex seedOccurrence.root stage.unop)
    ext degree localValue
    by_cases degreeZero : degree = 0
    · subst degree
      exact CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.carrierReversal_involutive
        seedOccurrence.root stage.unop localValue
    · let targetSubsingleton : Subsingleton
          ((ActualComplex seedOccurrence.root stage.unop).X degree : Type) := by
        dsimp only [ActualComplex]
        rw [if_neg degreeZero]
        infer_instance
      exact @Subsingleton.elim _ targetSubsingleton _ _
  have globalInvolutive :
      globalIntegralReversal ≫ globalIntegralReversal =
        𝟙 (limit (solutionDiagram seedOccurrence.root)) := by
    change
      limMap (integralReversalNatTrans seedOccurrence.root) ≫
          limMap (integralReversalNatTrans seedOccurrence.root) =
        𝟙 (limit (solutionDiagram seedOccurrence.root))
    apply limit.hom_ext
    intro stage
    calc
      (limMap (integralReversalNatTrans seedOccurrence.root) ≫
          limMap (integralReversalNatTrans seedOccurrence.root)) ≫
          limit.π (solutionDiagram seedOccurrence.root) stage =
        limit.π (solutionDiagram seedOccurrence.root) stage ≫
          ((integralReversalNatTrans seedOccurrence.root).app stage ≫
            (integralReversalNatTrans seedOccurrence.root).app stage) := by
              rw [Category.assoc, limMap_π, ← Category.assoc,
                limMap_π, Category.assoc]
      _ = limit.π (solutionDiagram seedOccurrence.root) stage := by
        rw [localInvolutive, Category.comp_id]
      _ = 𝟙 _ ≫
          limit.π (solutionDiagram seedOccurrence.root) stage := by
            rw [Category.id_comp]
  exact congrArg
    (fun arrow :
      limit (solutionDiagram seedOccurrence.root) ⟶
        limit (solutionDiagram seedOccurrence.root) =>
      (arrow.f 0).hom value)
    globalInvolutive

end
end CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
