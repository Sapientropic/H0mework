import Mathlib.Data.Nat.Find
import H0mework.Arithmetic.GoldbachFourier.ClassicalBridge
import H0mework.Arithmetic.Goldbach.RiemannJointConsumer

/-!
# Coverage-complete global Goldbach disposition

The global classical mouth is settled into exactly two generated branches:

* the classical statement, together with all named positive faces; or
* the first classical-range index carrying a faithful effective residual.

The negative branch stores the actual residual, minimality, the joint named
arithmetic consumer, whole-ledger write-back, and generated next.  It is
derived from failure of the classical statement through the already checked
coverage equivalence; no residual or branch is a caller premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticGlobalGoldbachDisposition

open CanonicalUnitArithmeticClassicalGoldbachBridge
open CanonicalUnitArithmeticEffectiveAdditiveConsumer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticGoldbachRiemannJointConsumer
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

def ClassicalRangeFailureAt (index : Nat) : Prop :=
  1 ≤ index ∧ ¬ Nonempty (EffectiveAdditiveFibreAt index)

theorem exists_failure_of_not_classical
    (notClassical : ¬ CanonicalClassicalGoldbach) :
    ∃ index, ClassicalRangeFailureAt index := by
  have notEffective : ¬ AllClassicalRangeEffectiveFibres := by
    intro effective
    exact notClassical (classical_of_effectiveFibres effective)
  by_contra noFailure
  apply notEffective
  intro index indexInRange
  by_contra fibreEmpty
  exact noFailure ⟨index, indexInRange, fibreEmpty⟩

noncomputable def firstFailureIndex
    (notClassical : ¬ CanonicalClassicalGoldbach) : Nat :=
  by
    classical
    exact Nat.find (exists_failure_of_not_classical notClassical)

theorem firstFailureIndex_spec
    (notClassical : ¬ CanonicalClassicalGoldbach) :
    ClassicalRangeFailureAt (firstFailureIndex notClassical) := by
  classical
  exact Nat.find_spec (exists_failure_of_not_classical notClassical)

theorem prior_fibre_inhabited
    (notClassical : ¬ CanonicalClassicalGoldbach)
    {prior : Nat} (priorInRange : 1 ≤ prior)
    (prior_lt : prior < firstFailureIndex notClassical) :
    Nonempty (EffectiveAdditiveFibreAt prior) := by
  classical
  by_contra fibreEmpty
  exact (Nat.find_min (exists_failure_of_not_classical notClassical)
    prior_lt) ⟨priorInRange, fibreEmpty⟩

/-- First exact failed dependent face in the classical range. -/
structure FirstResidualOccurrence : Type where
  index : Nat
  indexInRange : 1 ≤ index
  fibreEmpty : ¬ Nonempty (EffectiveAdditiveFibreAt index)
  priorPositive : ∀ prior : Nat, 1 ≤ prior → prior < index →
    Nonempty (EffectiveAdditiveFibreAt prior)
  residual : EffectiveAdditiveResidualAt index
  disposition_eq :
    generatedAdditiveDisposition index = .residual residual
  residualConsumer : ResidualConsumesAt index residual

noncomputable def generateFirstResidual
    (notClassical : ¬ CanonicalClassicalGoldbach) :
    FirstResidualOccurrence := by
  let index := firstFailureIndex notClassical
  have failure : ClassicalRangeFailureAt index :=
    firstFailureIndex_spec notClassical
  let residual : EffectiveAdditiveResidualAt index :=
    residualOfEmpty (additiveEvaluation index) (evenTargetHistory index)
      failure.2
  exact
    { index := index
      indexInRange := failure.1
      fibreEmpty := failure.2
      priorPositive := fun prior priorInRange prior_lt =>
        prior_fibre_inhabited notClassical priorInRange prior_lt
      residual := residual
      disposition_eq :=
        settle_eq_residual_of_empty _ _ failure.2
      residualConsumer := consumeResidual residual }

namespace FirstResidualOccurrence

def jointConsumer (failure : FirstResidualOccurrence) :
    JointConsumesAt failure.index :=
  CanonicalUnitArithmeticGoldbachRiemannJointConsumer.consume failure.index

end FirstResidualOccurrence

/-- Coverage-complete global result.  The positive branch also supplies the
pointwise joint consumer; the negative branch contains the first exact
residual occurrence. -/
inductive GlobalDisposition : Type 7 where
  | positive
      (classical : CanonicalClassicalGoldbach)
      (namedPositive : AllNamedGoldbachDispositionsPositive)
      (joint : ∀ index : Nat, JointConsumesAt index)
  | firstResidual
      (notClassical : ¬ CanonicalClassicalGoldbach)
      (failure : FirstResidualOccurrence)

noncomputable def settle : GlobalDisposition := by
  classical
  by_cases classical : CanonicalClassicalGoldbach
  · exact .positive classical
      (classical_iff_namedPositive.mp classical)
      CanonicalUnitArithmeticGoldbachRiemannJointConsumer.consume
  · exact .firstResidual classical (generateFirstResidual classical)

theorem total : Nonempty GlobalDisposition :=
  ⟨settle⟩

theorem no_firstResidual_of_classical
    (classical : CanonicalClassicalGoldbach) :
    IsEmpty FirstResidualOccurrence := by
  constructor
  intro failure
  have effective := effectiveFibres_of_classical classical
    failure.index failure.indexInRange
  exact failure.fibreEmpty effective

theorem not_classical_of_firstResidual
    (failure : FirstResidualOccurrence) :
    ¬ CanonicalClassicalGoldbach := by
  intro classical
  exact (no_firstResidual_of_classical classical).false failure

theorem classical_of_no_firstResidual
    (noFailure : IsEmpty FirstResidualOccurrence) :
    CanonicalClassicalGoldbach := by
  by_contra notClassical
  exact noFailure.false (generateFirstResidual notClassical)

theorem classical_iff_no_firstResidual :
    CanonicalClassicalGoldbach ↔ IsEmpty FirstResidualOccurrence :=
  ⟨no_firstResidual_of_classical, classical_of_no_firstResidual⟩

theorem positive_or_firstResidual :
    CanonicalClassicalGoldbach ∨ Nonempty FirstResidualOccurrence := by
  cases settled : settle with
  | positive classical _named _joint => exact .inl classical
  | firstResidual _notClassical failure => exact .inr ⟨failure⟩

end
end CanonicalUnitArithmeticGlobalGoldbachDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
