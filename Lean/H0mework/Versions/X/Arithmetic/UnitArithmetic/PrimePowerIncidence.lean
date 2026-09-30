import Mathlib.Data.Fin.Rev
import H0mework.Versions.X.Arithmetic.UnitArithmetic.Root
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Relations.FiniteDefectDeterminant
import H0mework.Realization.GlobalSections.KernelIncidenceRigidity

/-!
# Canonical unit arithmetic prime-power incidence

The first exact unit-root visit generates a finite free reversal relation
presentation.  Its cokernel is the finite-stage anti-invariant carrier.  An
evaluator is obtained by folding that same rooted domain occurrence, and its
prime-power landing relation is installed in one dependent occurrence before
the generic rigidity engine is invoked.

No kernel-zero, injectivity, equivalence, determinant, or coverage witness is
accepted by the source mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticPrimePowerIncidence

open CanonicalUnitArithmeticRoot
open AdditiveFamilyFaithfulRealization
open AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt
open FiniteDefectDeterminant
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open RootArithmeticUnfoldingFace

noncomputable section

/-- The relation rank is read from the exact initial whole unit history. -/
abbrev RelationRank : Nat :=
  CanonicalUnitArithmeticRoot.initialStep.material.whole.cardinalShadow

/-- Generated finite free relation lattice. -/
abbrev RelationLattice := Fin RelationRank → ℤ

/-- Actual reversal on the finite restriction. -/
def reversal : RelationLattice →ₗ[ℤ] RelationLattice where
  toFun := fun value index => value index.rev
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar value
    rfl

@[simp] theorem reversal_apply (value : RelationLattice)
    (index : Fin RelationRank) :
    reversal value index = value index.rev :=
  rfl

theorem reversal_involutive : Function.Involutive reversal := by
  intro value
  funext index
  simp [reversal]

/-- The anti-invariant relation is `x + ιx`; quotienting by its image forces
the reversal direction to act by sign. -/
def antiInvariantRelationMap : RelationLattice →ₗ[ℤ] RelationLattice :=
  LinearMap.id + reversal

def sourceOccurrences (value : RelationLattice) :
    RootedAccountedUnfolding RelationLattice :=
  RootedAccountedUnfolding.zero value

def targetOccurrences (value : RelationLattice) :
    RootedAccountedUnfolding RelationLattice :=
  RootedAccountedUnfolding.zero value

def relationMapOccurrence :
    RootedAccountedUnfolding (RelationLattice →ₗ[ℤ] RelationLattice) :=
  RootedAccountedUnfolding.zero antiInvariantRelationMap

abbrev DomainPoint : Type :=
  RootArithmeticDomainPointAt
    CanonicalUnitArithmeticRoot.initialStep PUnit

def rootOccurrence : RootedAccountedUnfolding DomainPoint :=
  CanonicalUnitArithmeticRoot.initialDomainOccurrence

/-- The existing generic finite-presentation owner is indexed by the exact
unit-root domain occurrence. -/
def presentation : RootGeneratedFiniteDefectPresentationAt
    rootOccurrence
      sourceOccurrences targetOccurrences relationMapOccurrence :=
  RootGeneratedFiniteDefectPresentationAt.generate

/-- Finite-stage anti-invariant relation carrier.  Removing the exact
presentation removes this type. -/
abbrev AntiInvariantCarrier : Type := presentation.cokernel

/-- Finite generation is inherited from the finite free target and its
generated quotient; it is not a caller field. -/
theorem generatedFinitePresentationFG : AddGroup.FG AntiInvariantCarrier := by
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

/-- The whole family of actual prime-power restrictions of the generated
anti-invariant carrier. -/
abbrev PrimePowerState :=
  PrimePowerQuotientEvaluation.State AntiInvariantCarrier

/-- Generic quotient evaluation installed by folding its universal law over
the exact unit occurrence. -/
def quotientEvaluationFace :
    RootGeneratedPrimePowerQuotientEvaluationAt AntiInvariantCarrier
      rootOccurrence generatedFinitePresentationFG :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate AntiInvariantCarrier

def foldGeneratedEvaluator : AntiInvariantCarrier → PrimePowerState :=
  quotientEvaluationFace.accountedEvaluator

@[simp] theorem foldGeneratedEvaluator_apply (value : AntiInvariantCarrier) :
    foldGeneratedEvaluator value =
      PrimePowerQuotientEvaluation.evaluator AntiInvariantCarrier value := by
  exact congrFun
    quotientEvaluationFace.accountedEvaluator_eq_canonical value

/-- The domain supplies only the generated carrier/FG; the generic kernel
packages zero, addition, naturality, quotient-zero, range membership, and
actual division roots. -/
def primePowerMaterial :
    PrimePowerKernelIncidenceAt AntiInvariantCarrier PrimePowerState :=
  quotientEvaluationFace.material

/-- One dependent occurrence carries both the exact unit-root domain point
and its actual prime-power incidence material. -/
def dependentOccurrence : RootedAccountedUnfolding
    (DomainPoint ×
      PrimePowerKernelIncidenceAt AntiInvariantCarrier PrimePowerState) :=
  quotientEvaluationFace.dependentOccurrence

def rigidityFace : RootGeneratedPrimePowerKernelIncidenceRigidityAt
    dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

/-- The generic engine, not the domain mouth, generates residual zero. -/
theorem sourceKernelResidualZero :
    GeneratedSourceKernelResidualZeroAt rigidityFace.faithfulFace
      rigidityFace.additiveCalculation :=
  rigidityFace.sourceKernelResidualZero

/-- The generic engine, not the domain mouth, generates the canonical source
component equivalence. -/
noncomputable def canonicalSourceComponentEquiv :=
  rigidityFace.canonicalSourceComponentEquiv

theorem rigidity_preserves_exact_unit_occurrence :
    rigidityFace.root =
      CanonicalUnitArithmeticRoot.initialDomainOccurrence := by
  exact quotientEvaluationFace.dependentOccurrence_projects_to_root

theorem rigidity_uses_fold_evaluator_and_actual_division_landing :
    rigidityFace.actualMaterial.evaluator = foldGeneratedEvaluator ∧
      (∀ (element : AntiInvariantCarrier),
        foldGeneratedEvaluator element = 0 →
        ∀ (prime : Nat.Primes) (exponent : Nat), 0 < exponent →
          Nonempty { root : AntiInvariantCarrier //
            (prime : Nat) ^ exponent • root = element }) := by
  constructor
  · rfl
  · intro element evaluatorZero prime exponent exponentPositive
    exact ⟨primePowerMaterial.divisionRoot element evaluatorZero
      prime exponent exponentPositive⟩

theorem rigidity_reuses_root_whole_ledger_and_next :
    HEq CanonicalUnitArithmeticRoot.initialDomainAdmission.wholeLedgerWriteBack
        CanonicalUnitArithmeticRoot.initialStep.wholeLedgerWriteBack ∧
      CanonicalUnitArithmeticRoot.initialDomainAdmission.nextCurrent =
        CanonicalUnitArithmeticRoot.livingRoot.generatedNextCurrentAt
          CanonicalUnitArithmeticRoot.initialVisit :=
  CanonicalUnitArithmeticRoot.initialDomain_reuses_whole_ledger_and_next

end

end CanonicalUnitArithmeticPrimePowerIncidence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
