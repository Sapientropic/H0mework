import Mathlib.Data.Nat.Factorization.Basic
import H0mework.Versions.X.Arithmetic.GoldbachDynamics.FactorOrbit

/-!
# Source-generated full-factor repair law

The canonical orbit selects `Nat.minFac` as one ordered spine.  This producer
retains every actual prime divisor of either composite endpoint and turns it
into the same effectivity-preserving repair step.  Targets are calculated
by the repair law; callers provide neither a landing nor a target-equivalent
premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFullFactorRepairProducer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer

noncomputable section

/-- All source-generated prime-factor choices at either composite endpoint.
The classifier may keep a left-first canonical spine, but the branching step
type retains both directions. -/
inductive FactorRepairAlternativeAt {index : Nat}
    (source : EffectiveSplitAt index) : Type
  | left
      (leftNotPrime : ¬ Nat.Prime (splitLeft source))
      (factor : {p : Nat // p ∈ (splitLeft source).primeFactors})
  | right
      (rightNotPrime : ¬ Nat.Prime (splitRight source))
      (factor : {p : Nat // p ∈ (splitRight source).primeFactors})

namespace FactorRepairAlternativeAt

variable {index : Nat} {source : EffectiveSplitAt index}

def factor : FactorRepairAlternativeAt source → Nat
  | .left _ factor => factor.1
  | .right _ factor => factor.1

theorem factorPrime (alternative : FactorRepairAlternativeAt source) :
    Nat.Prime alternative.factor := by
  cases alternative with
  | left _ factor => exact Nat.prime_of_mem_primeFactors factor.2
  | right _ factor => exact Nat.prime_of_mem_primeFactors factor.2

theorem factorDvd (alternative : FactorRepairAlternativeAt source) :
    alternative.factor ∣
      match alternative with
      | .left _ _ => splitLeft source
      | .right _ _ => splitRight source := by
  cases alternative with
  | left _ factor => exact Nat.dvd_of_mem_primeFactors factor.2
  | right _ factor => exact Nat.dvd_of_mem_primeFactors factor.2

theorem factorProper (alternative : FactorRepairAlternativeAt source) :
    alternative.factor <
      match alternative with
      | .left _ _ => splitLeft source
      | .right _ _ => splitRight source := by
  cases alternative with
  | left leftNotPrime factor =>
      have endpointPos : 0 < splitLeft source := by
        have endpointFloor := splitLeft_atLeastTwo source
        omega
      have factorLe : factor.1 ≤ splitLeft source :=
        Nat.le_of_dvd endpointPos
          (Nat.dvd_of_mem_primeFactors factor.2)
      have factorNe : factor.1 ≠ splitLeft source := by
        intro factorEq
        apply leftNotPrime
        simpa [factorEq] using Nat.prime_of_mem_primeFactors factor.2
      exact lt_of_le_of_ne factorLe factorNe
  | right rightNotPrime factor =>
      have endpointPos : 0 < splitRight source := by
        have endpointFloor := splitRight_atLeastTwo source
        omega
      have factorLe : factor.1 ≤ splitRight source :=
        Nat.le_of_dvd endpointPos
          (Nat.dvd_of_mem_primeFactors factor.2)
      have factorNe : factor.1 ≠ splitRight source := by
        intro factorEq
        apply rightNotPrime
        simpa [factorEq] using Nat.prime_of_mem_primeFactors factor.2
      exact lt_of_le_of_ne factorLe factorNe

def properFactorization (alternative : FactorRepairAlternativeAt source) :
    ProperFactorizationAt
      (match alternative with
      | .left _ _ => splitLeft source
      | .right _ _ => splitRight source) :=
  properFactorizationOfPrimeDivisor _ alternative.factor
    alternative.factorPrime alternative.factorDvd alternative.factorProper

def step (alternative : FactorRepairAlternativeAt source) :
    FactorRepairStepAt source := by
  cases alternative with
  | left leftNotPrime factor =>
      let alternative : FactorRepairAlternativeAt source :=
        .left leftNotPrime factor
      exact .left
        (generateLeftFactorRepair source alternative.properFactorization)
  | right rightNotPrime factor =>
      let alternative : FactorRepairAlternativeAt source :=
        .right rightNotPrime factor
      exact .right
        (generateRightFactorRepair source alternative.properFactorization)

def target (alternative : FactorRepairAlternativeAt source) :
    EffectiveSplitAt index := alternative.step.target

theorem target_lands (alternative : FactorRepairAlternativeAt source) :
    splitLeft alternative.target + splitRight alternative.target =
      repairTargetValue index :=
  split_landing alternative.target

theorem left_target_left
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    splitLeft
        ((FactorRepairAlternativeAt.left leftNotPrime selected).target) =
      splitLeft source - (selected.1 - 1) := by
  let alternative : FactorRepairAlternativeAt source :=
    .left leftNotPrime selected
  change splitLeft
      (generateLeftFactorRepair source alternative.properFactorization).target =
    splitLeft source - (selected.1 - 1)
  rw [(generateLeftFactorRepair source alternative.properFactorization).leftReadout,
    (generateLeftFactorRepair source alternative.properFactorization).shift_eq,
    factorShift]
  rfl

theorem left_target_strict
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    splitLeft
        ((FactorRepairAlternativeAt.left leftNotPrime selected).target) <
      splitLeft source := by
  let alternative : FactorRepairAlternativeAt source :=
    .left leftNotPrime selected
  exact (generateLeftFactorRepair source
    alternative.properFactorization).leftStrict

theorem left_selectedFactorProper
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    selected.1 < splitLeft source := by
  simpa only [factor] using
    FactorRepairAlternativeAt.factorProper
      (FactorRepairAlternativeAt.left leftNotPrime selected)

theorem right_target_left
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    splitLeft
        ((FactorRepairAlternativeAt.right rightNotPrime selected).target) =
      splitLeft source + (selected.1 - 1) := by
  let alternative : FactorRepairAlternativeAt source :=
    .right rightNotPrime selected
  change splitLeft
      (generateRightFactorRepair source alternative.properFactorization).target =
    splitLeft source + (selected.1 - 1)
  rw [(generateRightFactorRepair source alternative.properFactorization).leftReadout,
    (generateRightFactorRepair source alternative.properFactorization).shift_eq,
    factorShift]
  rfl

theorem right_target_strict
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    splitLeft source <
      splitLeft
        ((FactorRepairAlternativeAt.right rightNotPrime selected).target) := by
  let alternative : FactorRepairAlternativeAt source :=
    .right rightNotPrime selected
  change splitLeft source < splitLeft
    (generateRightFactorRepair source
      alternative.properFactorization).target
  have leftReadout := (generateRightFactorRepair source
    alternative.properFactorization).leftReadout
  have shiftPositive := (generateRightFactorRepair source
    alternative.properFactorization).shiftPositive
  omega

theorem right_selectedFactorProper
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    selected.1 < splitRight source := by
  simpa only [factor] using
    FactorRepairAlternativeAt.factorProper
      (FactorRepairAlternativeAt.right rightNotPrime selected)

end FactorRepairAlternativeAt

end
end CanonicalUnitArithmeticFullFactorRepairProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
