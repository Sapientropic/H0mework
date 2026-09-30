import H0mework.Versions.X.Arithmetic.UnitArithmetic.EulerPrefix
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Relations.FiniteDefectDeterminant

/-!
# Cofinal bare-reversal relation diagram

Every generated unit/prime stage owns a dual pair of integral generators.
Reversal flips only the dual bit, so canonical restriction from stage `n+1`
to `n` commutes with reversal and with the anti-invariant boundary.

The scalar called `stageEulerWeight` below is retained as a negative
calibration: it is provably `1`, so this module supplies pure-reversal
infrastructure only.  The authoritative Euler-coupled carrier is the
prime/exponent convolution operator in
`LivingLawCanonicalUnitArithmeticPrimeExponentEulerOperator`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCofinalReversalRelation

open CanonicalUnitArithmeticCofinalEulerPrefix
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticPrimePowerIncidence
open FiniteDefectDeterminant
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt

noncomputable section

def canonicalSource : CoordinateFreeRelationSource :=
  commonOccurrence.root.2

abbrev StageRank (stage : Nat) : Nat :=
  (cofinalHistory canonicalSource stage).cardinalShadow

abbrev StageIndex (stage : Nat) : Type :=
  Fin (StageRank stage) × Fin 2

abbrev StageRelationLattice (stage : Nat) : Type :=
  StageIndex stage → ℤ

/-- Stable reversal flips the dual bit and preserves the stage coordinate. -/
def stageReversal (stage : Nat) :
    StageRelationLattice stage →ₗ[ℤ] StageRelationLattice stage where
  toFun := fun value index => value (index.1, index.2.rev)
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar value
    rfl

@[simp] theorem stageReversal_apply
    (stage : Nat) (value : StageRelationLattice stage)
    (index : StageIndex stage) :
    stageReversal stage value index = value (index.1, index.2.rev) :=
  rfl

theorem stageReversal_involutive (stage : Nat) :
    Function.Involutive (stageReversal stage) := by
  intro value
  funext index
  simp [stageReversal]

/-- Legacy scalar coefficient; the following theorem proves that it carries
no Euler-action information. -/
def stageEulerWeight (stage : Nat) (index : Fin (StageRank stage)) : ℤ :=
  sourceLocalFormalEulerFactor (primeAtStage index)
    (primeAtStage index : Nat)

@[simp] theorem stageEulerWeight_eq_one
    (stage : Nat) (index : Fin (StageRank stage)) :
    stageEulerWeight stage index = 1 := by
  unfold stageEulerWeight
  simpa using sourceLocalFormalEulerFactor_apply_primePower
    (primeAtStage index) 1

/-- Calibration wrapper which collapses to bare reversal. -/
def weightedStageReversal (stage : Nat) :
    StageRelationLattice stage →ₗ[ℤ] StageRelationLattice stage where
  toFun := fun value index =>
    stageEulerWeight stage index.1 * value (index.1, index.2.rev)
  map_add' := by
    intro left right
    funext index
    simp [mul_add]
  map_smul' := by
    intro scalar value
    funext index
    simp

theorem weightedStageReversal_eq_reversal (stage : Nat) :
    weightedStageReversal stage = stageReversal stage := by
  ext value index
  simp [weightedStageReversal, stageReversal]

def stageBoundary (stage : Nat) :
    StageRelationLattice stage →ₗ[ℤ] StageRelationLattice stage :=
  LinearMap.id - weightedStageReversal stage

/-- Forget the newest unit/prime coordinate while retaining both dual
generators at every earlier stage. -/
def relationRestriction (stage : Nat) :
    StageRelationLattice (stage + 1) →ₗ[ℤ] StageRelationLattice stage where
  toFun := fun value index =>
    value (index.1.castSucc, index.2)
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar value
    rfl

@[simp] theorem relationRestriction_apply
    (stage : Nat) (value : StageRelationLattice (stage + 1))
    (index : StageIndex stage) :
    relationRestriction stage value index =
      value (index.1.castSucc, index.2) :=
  rfl

theorem relationRestriction_reversal_square (stage : Nat) :
    (relationRestriction stage).comp (stageReversal (stage + 1)) =
      (stageReversal stage).comp (relationRestriction stage) := by
  ext value index
  rfl

theorem relationRestriction_boundary_square (stage : Nat) :
    (relationRestriction stage).comp (stageBoundary (stage + 1)) =
      (stageBoundary stage).comp (relationRestriction stage) := by
  unfold stageBoundary
  rw [weightedStageReversal_eq_reversal (stage + 1),
    weightedStageReversal_eq_reversal stage]
  ext value index
  rfl

def stageSourceOccurrences (stage : Nat)
    (value : StageRelationLattice stage) :
    RootedAccountedUnfolding (StageRelationLattice stage) :=
  RootedAccountedUnfolding.zero value

def stageTargetOccurrences (stage : Nat)
    (value : StageRelationLattice stage) :
    RootedAccountedUnfolding (StageRelationLattice stage) :=
  RootedAccountedUnfolding.zero value

def stageBoundaryOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (StageRelationLattice stage →ₗ[ℤ] StageRelationLattice stage) :=
  (prefixOccurrence stage).map fun _point => stageBoundary stage

def stagePresentation (stage : Nat) :
    RootGeneratedFiniteDefectPresentationAt
      (prefixOccurrence stage)
      (stageSourceOccurrences stage)
      (stageTargetOccurrences stage)
      (stageBoundaryOccurrence stage) :=
  RootGeneratedFiniteDefectPresentationAt.generate

def StageCarrier (stage : Nat) : Type :=
  (stagePresentation stage).cokernel

instance stageCarrierAddCommGroup (stage : Nat) :
    AddCommGroup (StageCarrier stage) := by
  unfold StageCarrier
  infer_instance

instance stageCarrierModule (stage : Nat) :
    Module ℤ (StageCarrier stage) := by
  unfold StageCarrier
  infer_instance

theorem stageCarrierFG (stage : Nat) : AddGroup.FG (StageCarrier stage) := by
  let _ : Module.Finite ℤ (StageRelationLattice stage) := by
    infer_instance
  apply Module.Finite.iff_addGroup_fg.mp
  unfold StageCarrier
  exact Module.Finite.quotient ℤ
    (LinearMap.range (stageBoundary stage))

theorem relationRestriction_maps_boundaryRange (stage : Nat) :
    LinearMap.range (stageBoundary (stage + 1)) ≤
      (LinearMap.range (stageBoundary stage)).comap
        (relationRestriction stage) := by
  intro relation relationMem
  rcases relationMem with ⟨source, rfl⟩
  change relationRestriction stage (stageBoundary (stage + 1) source) ∈
    LinearMap.range (stageBoundary stage)
  rw [← LinearMap.comp_apply, relationRestriction_boundary_square,
    LinearMap.comp_apply]
  exact ⟨relationRestriction stage source, rfl⟩

/-- Actual map of generated cofibers induced by the boundary square. -/
def carrierRestriction (stage : Nat) :
    StageCarrier (stage + 1) →ₗ[ℤ] StageCarrier stage :=
  Submodule.mapQ
    (LinearMap.range (stageBoundary (stage + 1)))
    (LinearMap.range (stageBoundary stage))
    (relationRestriction stage)
    (relationRestriction_maps_boundaryRange stage)

def carrierRestrictionAddHom (stage : Nat) :
    StageCarrier (stage + 1) →+ StageCarrier stage :=
  (carrierRestriction stage).toAddHom

abbrev StagePrimePowerState (stage : Nat) :=
  PrimePowerQuotientEvaluation.State (StageCarrier stage)

def stageEvaluator (stage : Nat) :
    StageCarrier stage → StagePrimePowerState stage :=
  PrimePowerQuotientEvaluation.evaluator (StageCarrier stage)

def stageQuotientFace (stage : Nat) :
    RootGeneratedPrimePowerQuotientEvaluationAt (StageCarrier stage)
      (prefixOccurrence stage) (stageCarrierFG stage) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate (StageCarrier stage)

def stageDependentOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (((DomainPoint × CoordinateFreeRelationSource) × ArithmeticFunction ℤ) ×
        PrimePowerKernelIncidenceAt
          (StageCarrier stage) (StagePrimePowerState stage)) :=
  (stageQuotientFace stage).dependentOccurrence

def stageRigidityFace (stage : Nat) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      (stageDependentOccurrence stage) :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem stageRigidity_projects_to_prefixOccurrence (stage : Nat) :
    (stageRigidityFace stage).root = prefixOccurrence stage :=
  (stageQuotientFace stage).dependentOccurrence_projects_to_root

/-- The cofiber restriction induces the expected square on every actual
prime-power quotient. -/
theorem primePowerRestriction_naturality
    (stage : Nat) (value : StageCarrier (stage + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    PrimePowerQuotientEvaluation.quotientMap
        (carrierRestrictionAddHom stage) prime exponent
        (stageEvaluator (stage + 1) value prime exponent) =
      stageEvaluator stage
        (carrierRestrictionAddHom stage value) prime exponent :=
  PrimePowerQuotientEvaluation.evaluator_naturality
    (carrierRestrictionAddHom stage) value prime exponent

end
end CanonicalUnitArithmeticCofinalReversalRelation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
