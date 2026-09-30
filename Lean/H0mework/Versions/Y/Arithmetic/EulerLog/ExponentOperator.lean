import H0mework.Realization.MappingCone.Functoriality
import H0mework.Versions.X.Arithmetic.UnitArithmetic.EulerLimit
import H0mework.Versions.X.Arithmetic.UnitArithmetic.RuntimeEuler
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Relations.FiniteDefectDeterminant
import H0mework.Realization.HomotopyLimits.Sequential

/-!
# Prime/exponent local Euler operator

This is the first relation tower whose action genuinely consumes the Euler
object.  For a fixed exponent depth, each stage is indexed by

`prime-stage × local exponent × dual bit`.

The local Euler action is truncated convolution by the full generated
prime-power coefficient family.  Its inverse-side relation operator is
truncated convolution by the actual local polynomial `1 - X`; neither is a
single coefficient.  Reversal flips the dual bit, and the coupled boundary
is `id - (Euler convolution ∘ reversal)`.

The authoritative tower is computed from the `GeneratedCofinalEulerLimit`
inside the same occurrence payload.  Replacing or deleting that payload
therefore changes or destroys the action itself; it is not a constant tower
attached after the fact.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticPrimeExponentEulerOperator

open AdditiveFamilyFaithfulRealization
open AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt
open CanonicalUnitArithmeticCofinalEulerLimit
open CanonicalUnitArithmeticCofinalEulerPrefix
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticPrimePowerIncidence
open CanonicalUnitArithmeticRuntimeCofinalEuler
open CategoryTheory
open CochainMappingCoconeFunctoriality
open FiniteDefectDeterminant
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open SequentialHomotopyLimit

noncomputable section

abbrev PrimeRank (stage : Nat) : Nat :=
  (runtimeWholeHistory stage).cardinalShadow

abbrev LocalExponent (depth : Nat) : Type := Fin (depth + 1)

abbrev EulerIndex (stage depth : Nat) : Type :=
  Fin (PrimeRank stage) × LocalExponent depth × Fin 2

abbrev EulerLattice (stage depth : Nat) : Type :=
  EulerIndex stage depth → ℤ

def exponentSub {depth : Nat} (exponent : LocalExponent depth)
    (amount : Nat) : LocalExponent depth :=
  ⟨exponent - amount, (Nat.sub_le exponent amount).trans_lt exponent.isLt⟩

theorem generatedLimit_eq_formalEulerCoefficients
    (generated : GeneratedCofinalEulerLimit) :
    generated.limit = formalEulerCoefficients :=
  cofinalEulerLimit_unique generated.generated
    (formalEulerCofinalLimit generated.source)

def generatedEulerCoefficient
    (generated : GeneratedCofinalEulerLimit)
    (primeIndex : Nat) (exponent : Nat) : ℤ :=
  generated.limit
    ((primeAtStage primeIndex : Nat) ^ exponent)

theorem generatedEulerCoefficient_eq_one
    (generated : GeneratedCofinalEulerLimit)
    (primeIndex exponent : Nat) :
    generatedEulerCoefficient generated primeIndex exponent = 1 := by
  rw [generatedEulerCoefficient,
    generatedLimit_eq_formalEulerCoefficients,
    formalEulerCoefficients_apply_primePower,
    localFormalEulerFactor_apply_primePower]

def localPolynomialCoefficient
    (primeIndex : Nat) (exponent : Nat) : ℤ :=
  (sourceLocalZetaPolynomial (primeAtStage primeIndex)).coeff exponent

@[simp] theorem localPolynomialCoefficient_zero (primeIndex : Nat) :
    localPolynomialCoefficient primeIndex 0 = 1 := by
  simp [localPolynomialCoefficient, sourceLocalZetaPolynomial]

@[simp] theorem localPolynomialCoefficient_one (primeIndex : Nat) :
    localPolynomialCoefficient primeIndex 1 = -1 := by
  simp [localPolynomialCoefficient, sourceLocalZetaPolynomial,
    Polynomial.coeff_one]

@[simp] theorem localPolynomialCoefficient_of_two_le
    (primeIndex exponent : Nat) (large : 2 ≤ exponent) :
    localPolynomialCoefficient primeIndex exponent = 0 := by
  simp [localPolynomialCoefficient, sourceLocalZetaPolynomial,
    Polynomial.coeff_X, Polynomial.coeff_one,
    (show exponent ≠ 0 by omega), (show (1 : Nat) ≠ exponent by omega)]

/-- Truncated local convolution by an actual prime-power coefficient
function. -/
def localEulerOperatorFor
    (limit : ArithmeticFunction ℤ) (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      limit ((primeAtStage index.1 : Nat) ^ amount) *
        value (index.1, exponentSub index.2.1 amount, index.2.2)
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

/-- Authoritative local Euler operator read directly from the runtime-owned
cofinal limit payload. -/
def localEulerOperator
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth :=
  localEulerOperatorFor generated.limit stage depth

/-- Truncated convolution by the local Euler polynomial itself. -/
def localEulerPolynomialOperator (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      localPolynomialCoefficient index.1 amount *
        value (index.1, exponentSub index.2.1 amount, index.2.2)
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

/-- Genuine local Euler action: although each zeta coefficient is `1`, the
whole operator is cumulative convolution across the exponent coordinate. -/
theorem localEulerOperator_apply
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat)
    (value : EulerLattice stage depth) (index : EulerIndex stage depth) :
    localEulerOperator generated stage depth value index =
      ∑ amount ∈ Finset.range (index.2.1 + 1),
        value (index.1, exponentSub index.2.1 amount, index.2.2) := by
  change
    (∑ amount ∈ Finset.range (index.2.1 + 1),
      generated.limit ((primeAtStage index.1 : Nat) ^ amount) *
        value (index.1, exponentSub index.2.1 amount, index.2.2)) = _
  apply Finset.sum_congr rfl
  intro amount _membership
  have coefficient :
      generated.limit ((primeAtStage index.1 : Nat) ^ amount) = 1 := by
    simpa [generatedEulerCoefficient] using
      generatedEulerCoefficient_eq_one generated index.1 amount
  rw [coefficient, one_mul]

def exponentZeroBasis (stage depth : Nat)
    (primeIndex : Fin (PrimeRank stage)) (dualIndex : Fin 2) :
    EulerLattice stage depth :=
  Pi.single (primeIndex, (0 : LocalExponent depth), dualIndex) 1

def exponentOne (depth : Nat) : LocalExponent (depth + 1) :=
  ⟨1, by omega⟩

theorem localEulerOperatorFor_reads_prime_coefficient
    (limit : ArithmeticFunction ℤ) (stage depth : Nat)
    (primeIndex : Fin (PrimeRank stage)) (dualIndex : Fin 2) :
    localEulerOperatorFor limit stage (depth + 1)
        (exponentZeroBasis stage (depth + 1) primeIndex dualIndex)
        (primeIndex, exponentOne depth, dualIndex) =
      limit (primeAtStage primeIndex : Nat) := by
  change
    (∑ amount ∈ Finset.range 2,
      limit ((primeAtStage primeIndex : Nat) ^ amount) *
        exponentZeroBasis stage (depth + 1) primeIndex dualIndex
          (primeIndex, exponentSub (exponentOne depth) amount,
            dualIndex)) = _
  norm_num [exponentZeroBasis, exponentOne, exponentSub,
    Pi.single_apply, Finset.sum_range_succ]

/-- Semantic kill test: changing one local prime coefficient changes the
operator, before any quotient or determinant consumer. -/
theorem localEulerOperatorFor_ne_of_primeCoefficient_ne
    (left right : ArithmeticFunction ℤ) (stage depth : Nat)
    (primeIndex : Fin (PrimeRank stage)) (dualIndex : Fin 2)
    (different : left (primeAtStage primeIndex : Nat) ≠
      right (primeAtStage primeIndex : Nat)) :
    localEulerOperatorFor left stage (depth + 1) ≠
      localEulerOperatorFor right stage (depth + 1) := by
  intro sameOperator
  have sameValue := LinearMap.congr_fun sameOperator
    (exponentZeroBasis stage (depth + 1) primeIndex dualIndex)
  have sameCoefficient := congrFun sameValue
    (primeIndex, exponentOne depth, dualIndex)
  rw [localEulerOperatorFor_reads_prime_coefficient,
    localEulerOperatorFor_reads_prime_coefficient] at sameCoefficient
  exact different sameCoefficient

def stageReversal (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth where
  toFun := fun value index =>
    value (index.1, index.2.1, index.2.2.rev)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem stageReversal_involutive (stage depth : Nat) :
    Function.Involutive (stageReversal stage depth) := by
  intro value
  funext index
  simp [stageReversal]

/-- Concrete kill test: the full Euler convolution propagates an exponent-zero
basis vector to exponent one, whereas bare reversal cannot change the
exponent coordinate. -/
theorem localEulerOperator_differs_from_bare_reversal
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat)
    (primeIndex : Fin (PrimeRank stage)) (dualIndex : Fin 2) :
    localEulerOperator generated stage (depth + 1)
        (exponentZeroBasis stage (depth + 1) primeIndex dualIndex)
        (primeIndex, exponentOne depth, dualIndex) = 1 ∧
      stageReversal stage (depth + 1)
        (exponentZeroBasis stage (depth + 1) primeIndex dualIndex)
        (primeIndex, exponentOne depth, dualIndex) = 0 := by
  constructor
  · rw [localEulerOperator_apply]
    norm_num [exponentZeroBasis, exponentOne, exponentSub,
      Pi.single_apply, Finset.sum_range_succ]
    decide
  · simp [stageReversal, exponentZeroBasis, exponentOne]

/-- Euler convolution and reversal are coupled in one actual action. -/
def eulerReversalAction
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth :=
  (localEulerOperator generated stage depth).comp
    (stageReversal stage depth)

def stageBoundary
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth :=
  LinearMap.id - eulerReversalAction generated stage depth

/-- Drop only the newest prime stage; the full exponent fibre and dual bit
remain. -/
def relationRestriction (stage depth : Nat) :
    EulerLattice (stage + 1) depth →ₗ[ℤ] EulerLattice stage depth where
  toFun := fun value index =>
    value (index.1.castSucc, index.2.1, index.2.2)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem relationRestriction_euler_square
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    (relationRestriction stage depth).comp
        (localEulerOperator generated (stage + 1) depth) =
      (localEulerOperator generated stage depth).comp
        (relationRestriction stage depth) := by
  ext value index
  rfl

theorem relationRestriction_polynomial_square (stage depth : Nat) :
    (relationRestriction stage depth).comp
        (localEulerPolynomialOperator (stage + 1) depth) =
      (localEulerPolynomialOperator stage depth).comp
        (relationRestriction stage depth) := by
  ext value index
  rfl

theorem relationRestriction_reversal_square (stage depth : Nat) :
    (relationRestriction stage depth).comp
        (stageReversal (stage + 1) depth) =
      (stageReversal stage depth).comp
        (relationRestriction stage depth) := by
  ext value index
  rfl

theorem relationRestriction_action_square
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    (relationRestriction stage depth).comp
        (eulerReversalAction generated (stage + 1) depth) =
      (eulerReversalAction generated stage depth).comp
        (relationRestriction stage depth) := by
  ext value index
  rfl

theorem relationRestriction_boundary_square
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    (relationRestriction stage depth).comp
        (stageBoundary generated (stage + 1) depth) =
      (stageBoundary generated stage depth).comp
        (relationRestriction stage depth) := by
  ext value index
  rfl

def sourceOccurrences (stage depth : Nat)
    (value : EulerLattice stage depth) :
    RootedAccountedUnfolding (EulerLattice stage depth) :=
  RootedAccountedUnfolding.zero value

def targetOccurrences (stage depth : Nat)
    (value : EulerLattice stage depth) :
    RootedAccountedUnfolding (EulerLattice stage depth) :=
  RootedAccountedUnfolding.zero value

def boundaryOccurrence (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) : RootedAccountedUnfolding
      (EulerLattice stage depth →ₗ[ℤ] EulerLattice stage depth) :=
  (runtimeEulerPrefixOccurrence stage).map fun _root =>
    stageBoundary generated stage depth

def stagePresentation (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    RootGeneratedFiniteDefectPresentationAt
      (runtimeEulerPrefixOccurrence stage)
      (sourceOccurrences stage depth) (targetOccurrences stage depth)
      (boundaryOccurrence generated stage depth) :=
  RootGeneratedFiniteDefectPresentationAt.generate

def StageCarrier (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) : Type :=
  (stagePresentation generated stage depth).cokernel

instance stageCarrierAddCommGroup (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) : AddCommGroup (StageCarrier generated stage depth) := by
  unfold StageCarrier
  infer_instance

instance stageCarrierModule (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) : Module ℤ (StageCarrier generated stage depth) := by
  unfold StageCarrier
  infer_instance

theorem stageCarrierFG (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) : AddGroup.FG (StageCarrier generated stage depth) := by
  let _ : Module.Finite ℤ (EulerLattice stage depth) := by infer_instance
  apply Module.Finite.iff_addGroup_fg.mp
  unfold StageCarrier
  exact Module.Finite.quotient ℤ
    (LinearMap.range (stageBoundary generated stage depth))

theorem relationRestriction_maps_boundaryRange
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    LinearMap.range (stageBoundary generated (stage + 1) depth) ≤
      (LinearMap.range (stageBoundary generated stage depth)).comap
        (relationRestriction stage depth) := by
  intro relation relationMem
  rcases relationMem with ⟨source, rfl⟩
  change relationRestriction stage depth
      (stageBoundary generated (stage + 1) depth source) ∈
    LinearMap.range (stageBoundary generated stage depth)
  rw [← LinearMap.comp_apply,
    relationRestriction_boundary_square, LinearMap.comp_apply]
  exact ⟨relationRestriction stage depth source, rfl⟩

def carrierRestriction (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    StageCarrier generated (stage + 1) depth →ₗ[ℤ]
      StageCarrier generated stage depth :=
  Submodule.mapQ
    (LinearMap.range (stageBoundary generated (stage + 1) depth))
    (LinearMap.range (stageBoundary generated stage depth))
    (relationRestriction stage depth)
    (relationRestriction_maps_boundaryRange generated stage depth)

def carrierRestrictionAddHom (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    StageCarrier generated (stage + 1) depth →+
      StageCarrier generated stage depth :=
  (carrierRestriction generated stage depth).toAddHom

abbrev StagePrimePowerState (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :=
  PrimePowerQuotientEvaluation.State
    (StageCarrier generated stage depth)

def stageQuotientFace (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    RootGeneratedPrimePowerQuotientEvaluationAt
      (StageCarrier generated stage depth)
      (runtimeEulerPrefixOccurrence stage)
      (stageCarrierFG generated stage depth) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate
    (StageCarrier generated stage depth)

def stageEvaluator (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    StageCarrier generated stage depth →
      StagePrimePowerState generated stage depth :=
  (stageQuotientFace generated stage depth).accountedEvaluator

/-- The generic quotient naturality now runs on a carrier whose defining
boundary contains the actual Euler convolution, local polynomial and
reversal.  It is still a consumer; no local landing is claimed here. -/
theorem primePowerRestriction_naturality
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat)
    (value : StageCarrier generated (stage + 1) depth)
    (prime : Nat.Primes) (exponent : Nat) :
    PrimePowerQuotientEvaluation.quotientMap
        (carrierRestrictionAddHom generated stage depth) prime exponent
        (stageEvaluator generated (stage + 1) depth value prime exponent) =
      stageEvaluator generated stage depth
        (carrierRestrictionAddHom generated stage depth value)
          prime exponent :=
  PrimePowerQuotientEvaluation.evaluator_naturality
    (carrierRestrictionAddHom generated stage depth)
      value prime exponent

/-- One actual Euler/polynomial/reversal relation class. -/
def boundaryClass (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) (source : EulerLattice stage depth) :
    StageCarrier generated stage depth := by
  unfold StageCarrier
  exact Submodule.Quotient.mk
    (stageBoundary generated stage depth source)

theorem boundaryClass_eq_zero (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) (source : EulerLattice stage depth) :
    boundaryClass generated stage depth source = 0 := by
  unfold boundaryClass StageCarrier
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨source, rfl⟩

/-- Domain-generated quotient-zero incidence for an actual coupled boundary
class.  Division roots remain framework-owned. -/
theorem boundaryClass_quotientZero
    (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) (source : EulerLattice stage depth)
    (prime : Nat.Primes) (exponent : Nat) :
    stageEvaluator generated stage depth
        (boundaryClass generated stage depth source) prime exponent = 0 := by
  rw [boundaryClass_eq_zero]
  exact congrFun (congrFun
    (stageQuotientFace generated stage depth).material.zeroLanding prime)
      exponent

def boundaryClassDivisionRoot
    (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) (source : EulerLattice stage depth)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    { root : StageCarrier generated stage depth //
      (prime : Nat) ^ exponent • root =
        boundaryClass generated stage depth source } := by
  apply (stageQuotientFace generated stage depth).material.divisionRoot
  · funext localPrime localExponent
    exact boundaryClass_quotientZero generated stage depth source
      localPrime localExponent
  · exact positive

def stageDependentOccurrence (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :=
  (stageQuotientFace generated stage depth).dependentOccurrence

def stageRigidityFace (generated : GeneratedCofinalEulerLimit)
    (stage depth : Nat) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      (stageDependentOccurrence generated stage depth) :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem stageSourceKernelResidualZero
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    GeneratedSourceKernelResidualZeroAt
      (stageRigidityFace generated stage depth).faithfulFace
      (stageRigidityFace generated stage depth).additiveCalculation :=
  (stageRigidityFace generated stage depth).sourceKernelResidualZero

noncomputable abbrev StageLatticeModule (stage depth : Nat) :
    ModuleCat.{0} ℤ := ModuleCat.of ℤ (EulerLattice stage depth)

noncomputable abbrev stageLatticeComplex (stage depth : Nat) :
    IntegralCochainComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (StageLatticeModule stage depth)

noncomputable def stageBoundaryMap
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    stageLatticeComplex stage depth ⟶ stageLatticeComplex stage depth :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (stageBoundary generated stage depth))

noncomputable abbrev stageComplex
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    IntegralCochainComplex :=
  CochainComplex.mappingCocone (stageBoundaryMap generated stage depth)

noncomputable def stageLatticeRestriction (stage depth : Nat) :
    stageLatticeComplex (stage + 1) depth ⟶
      stageLatticeComplex stage depth :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (relationRestriction stage depth))

theorem stageLatticeRestriction_boundary_square
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    stageLatticeRestriction stage depth ≫
        stageBoundaryMap generated stage depth =
      stageBoundaryMap generated (stage + 1) depth ≫
        stageLatticeRestriction stage depth := by
  unfold stageLatticeRestriction stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact (relationRestriction_boundary_square generated stage depth).symm

noncomputable def stageTransition
    (generated : GeneratedCofinalEulerLimit) (stage depth : Nat) :
    stageComplex generated (stage + 1) depth ⟶
      stageComplex generated stage depth :=
  mappingCoconeMap
    (stageBoundaryMap generated (stage + 1) depth)
    (stageBoundaryMap generated stage depth)
    (stageLatticeRestriction stage depth)
    (stageLatticeRestriction stage depth)
    (stageLatticeRestriction_boundary_square generated stage depth)

noncomputable def relationTowerAt
    (generated : GeneratedCofinalEulerLimit) (depth : Nat) :
    ℕᵒᵖ ⥤ IntegralCochainComplex :=
  Functor.ofOpSequence
    (X := fun stage => stageComplex generated stage depth)
    (fun stage => stageTransition generated stage depth)

abbrev EulerTowerRoot :=
  RuntimeAuthority × GeneratedCofinalEulerLimit

/-- Unlike the rejected constant tower, the tower is calculated from the
actual `.limit` field inside each cofinal occurrence payload. -/
def dependentOccurrence (depth : Nat) : RootedAccountedUnfolding
    (EulerTowerRoot × (ℕᵒᵖ ⥤ IntegralCochainComplex)) :=
  runtimeCofinalLimitOccurrence.map fun root =>
    (root, relationTowerAt root.2 depth)

def homotopyLimitFace (depth : Nat) :
    RootGeneratedSequentialHomotopyLimitAt (dependentOccurrence depth) :=
  RootGeneratedSequentialHomotopyLimitAt.generate

theorem homotopyLimitFace_projects_to_cofinalOccurrence (depth : Nat) :
    (homotopyLimitFace depth).root = runtimeCofinalLimitOccurrence := by
  rw [RootGeneratedSequentialHomotopyLimitAt.root, dependentOccurrence,
    RootedAccountedUnfolding.map_map]
  change runtimeCofinalLimitOccurrence.map id = runtimeCofinalLimitOccurrence
  exact RootedAccountedUnfolding.map_id _

/-! ## Runtime diagonal: primes and exponent depth grow together -/

/-- Forget the newest prime and newest exponent coordinate in one actual
runtime step. -/
def diagonalRelationRestriction (stage : Nat) :
    EulerLattice (stage + 1) (stage + 1) →ₗ[ℤ]
      EulerLattice stage stage where
  toFun := fun value index =>
    value (index.1.castSucc, index.2.1.castSucc, index.2.2)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem diagonalRestriction_euler_square
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    (diagonalRelationRestriction stage).comp
        (localEulerOperator generated (stage + 1) (stage + 1)) =
      (localEulerOperator generated stage stage).comp
        (diagonalRelationRestriction stage) := by
  ext value index
  rfl

theorem diagonalRestriction_polynomial_square (stage : Nat) :
    (diagonalRelationRestriction stage).comp
        (localEulerPolynomialOperator (stage + 1) (stage + 1)) =
      (localEulerPolynomialOperator stage stage).comp
        (diagonalRelationRestriction stage) := by
  ext value index
  rfl

theorem diagonalRestriction_reversal_square (stage : Nat) :
    (diagonalRelationRestriction stage).comp
        (stageReversal (stage + 1) (stage + 1)) =
      (stageReversal stage stage).comp
        (diagonalRelationRestriction stage) := by
  ext value index
  rfl

theorem diagonalRestriction_action_square
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    (diagonalRelationRestriction stage).comp
        (eulerReversalAction generated (stage + 1) (stage + 1)) =
      (eulerReversalAction generated stage stage).comp
        (diagonalRelationRestriction stage) := by
  ext value index
  rfl

theorem diagonalRestriction_boundary_square
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    (diagonalRelationRestriction stage).comp
        (stageBoundary generated (stage + 1) (stage + 1)) =
      (stageBoundary generated stage stage).comp
        (diagonalRelationRestriction stage) := by
  ext value index
  rfl

noncomputable def diagonalLatticeRestrictionMap (stage : Nat) :
    stageLatticeComplex (stage + 1) (stage + 1) ⟶
      stageLatticeComplex stage stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (diagonalRelationRestriction stage))

theorem diagonalLatticeRestriction_boundary_square
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    diagonalLatticeRestrictionMap stage ≫
        stageBoundaryMap generated stage stage =
      stageBoundaryMap generated (stage + 1) (stage + 1) ≫
        diagonalLatticeRestrictionMap stage := by
  unfold diagonalLatticeRestrictionMap stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact (diagonalRestriction_boundary_square generated stage).symm

noncomputable def diagonalStageTransition
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageComplex generated (stage + 1) (stage + 1) ⟶
      stageComplex generated stage stage :=
  mappingCoconeMap
    (stageBoundaryMap generated (stage + 1) (stage + 1))
    (stageBoundaryMap generated stage stage)
    (diagonalLatticeRestrictionMap stage)
    (diagonalLatticeRestrictionMap stage)
    (diagonalLatticeRestriction_boundary_square generated stage)

/-- The authoritative cofinal diagram.  A single runtime index grows both
the prime prefix and the local exponent window. -/
noncomputable def diagonalRelationTowerAt
    (generated : GeneratedCofinalEulerLimit) :
    ℕᵒᵖ ⥤ IntegralCochainComplex :=
  Functor.ofOpSequence
    (X := fun stage => stageComplex generated stage stage)
    (diagonalStageTransition generated)

def diagonalDependentOccurrence : RootedAccountedUnfolding
    (EulerTowerRoot × (ℕᵒᵖ ⥤ IntegralCochainComplex)) :=
  runtimeCofinalLimitOccurrence.map fun root =>
    (root, diagonalRelationTowerAt root.2)

def diagonalHomotopyLimitFace :
    RootGeneratedSequentialHomotopyLimitAt diagonalDependentOccurrence :=
  RootGeneratedSequentialHomotopyLimitAt.generate

theorem diagonalHomotopyLimitFace_projects_to_runtimeOccurrence :
    diagonalHomotopyLimitFace.root = runtimeCofinalLimitOccurrence := by
  rw [RootGeneratedSequentialHomotopyLimitAt.root,
    diagonalDependentOccurrence, RootedAccountedUnfolding.map_map]
  change runtimeCofinalLimitOccurrence.map id = runtimeCofinalLimitOccurrence
  exact RootedAccountedUnfolding.map_id _

end
end CanonicalUnitArithmeticPrimeExponentEulerOperator
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
