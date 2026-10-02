import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.FactorRepair
import H0mework.Foundation.Finite.BranchingReachability

/-!
# Canonical full-factor repair reachability

All effective positive splits of the same generated even target form the
finite state carrier.  At either composite endpoint, every actual prime
divisor generates a repair edge.  The generic branching kernel therefore
returns an actual path to a prime-pair terminal or the complete reachable set
closed under every such factor edge.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFullFactorRepairReachabilityProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

def generatedLeftFactorAlternative {index : Nat}
    (source : EffectiveSplitAt index)
    (leftNotPrime : ¬ Nat.Prime (splitLeft source)) :
    FactorRepairAlternativeAt source := by
  let factor := Nat.minFac (splitLeft source)
  have factorPrime : Nat.Prime factor :=
    Nat.minFac_prime (by
      have endpointFloor := splitLeft_atLeastTwo source
      omega)
  have factorMem : factor ∈ (splitLeft source).primeFactors :=
    factorPrime.mem_primeFactors (Nat.minFac_dvd _) (by
      have endpointFloor := splitLeft_atLeastTwo source
      omega)
  exact .left leftNotPrime ⟨factor, factorMem⟩

def generatedRightFactorAlternative {index : Nat}
    (source : EffectiveSplitAt index)
    (rightNotPrime : ¬ Nat.Prime (splitRight source)) :
    FactorRepairAlternativeAt source := by
  let factor := Nat.minFac (splitRight source)
  have factorPrime : Nat.Prime factor :=
    Nat.minFac_prime (by
      have endpointFloor := splitRight_atLeastTwo source
      omega)
  have factorMem : factor ∈ (splitRight source).primeFactors :=
    factorPrime.mem_primeFactors (Nat.minFac_dvd _) (by
      have endpointFloor := splitRight_atLeastTwo source
      omega)
  exact .right rightNotPrime ⟨factor, factorMem⟩

theorem generatedLeftFactorAlternative_target_strict {index : Nat}
    (source : EffectiveSplitAt index)
    (leftNotPrime : ¬ Nat.Prime (splitLeft source)) :
    splitLeft (generatedLeftFactorAlternative source leftNotPrime).target <
      splitLeft source := by
  unfold generatedLeftFactorAlternative
  exact FactorRepairAlternativeAt.left_target_strict _ _

theorem generatedLeftFactorAlternative_factor_dvd {index : Nat}
    (source : EffectiveSplitAt index)
    (leftNotPrime : ¬ Nat.Prime (splitLeft source)) :
    (generatedLeftFactorAlternative source leftNotPrime).factor ∣
      splitLeft source := by
  unfold generatedLeftFactorAlternative
  exact FactorRepairAlternativeAt.factorDvd _

theorem generatedLeftFactorAlternative_factorProper {index : Nat}
    (source : EffectiveSplitAt index)
    (leftNotPrime : ¬ Nat.Prime (splitLeft source)) :
    (generatedLeftFactorAlternative source leftNotPrime).factor <
      splitLeft source := by
  unfold generatedLeftFactorAlternative
  exact FactorRepairAlternativeAt.factorProper _

theorem generatedLeftFactorAlternative_target_left {index : Nat}
    (source : EffectiveSplitAt index)
    (leftNotPrime : ¬ Nat.Prime (splitLeft source)) :
    splitLeft (generatedLeftFactorAlternative source leftNotPrime).target =
      splitLeft source -
        ((generatedLeftFactorAlternative source leftNotPrime).factor - 1) := by
  unfold generatedLeftFactorAlternative
  exact FactorRepairAlternativeAt.left_target_left _ _

theorem generatedRightFactorAlternative_target_strict {index : Nat}
    (source : EffectiveSplitAt index)
    (rightNotPrime : ¬ Nat.Prime (splitRight source)) :
    splitLeft source <
      splitLeft (generatedRightFactorAlternative source rightNotPrime).target := by
  unfold generatedRightFactorAlternative
  exact FactorRepairAlternativeAt.right_target_strict _ _

theorem generatedRightFactorAlternative_factor_dvd {index : Nat}
    (source : EffectiveSplitAt index)
    (rightNotPrime : ¬ Nat.Prime (splitRight source)) :
    (generatedRightFactorAlternative source rightNotPrime).factor ∣
      splitRight source := by
  unfold generatedRightFactorAlternative
  exact FactorRepairAlternativeAt.factorDvd _

theorem generatedRightFactorAlternative_target_left {index : Nat}
    (source : EffectiveSplitAt index)
    (rightNotPrime : ¬ Nat.Prime (splitRight source)) :
    splitLeft (generatedRightFactorAlternative source rightNotPrime).target =
      splitLeft source +
        ((generatedRightFactorAlternative source rightNotPrime).factor - 1) := by
  unfold generatedRightFactorAlternative
  exact FactorRepairAlternativeAt.right_target_left _ _

/-- The classifier supplies a canonical `minFac` step when nonterminal, but
the law's step type retains every actual prime-factor alternative. -/
noncomputable def fullFactorRepairLaw (index : Nat) :
    SourceGeneratedFiniteEffectiveBranchingReachability.Law
      (EffectiveSplitAt index) where
  TerminalAt := PrimePairTerminalAt
  StepAt := FactorRepairAlternativeAt
  target := FactorRepairAlternativeAt.target
  classify := by
    intro state
    by_cases leftPrime : Nat.Prime (splitLeft state)
    · by_cases rightPrime : Nat.Prime (splitRight state)
      · exact .inl ⟨leftPrime, rightPrime⟩
      · exact .inr
          (generatedRightFactorAlternative state rightPrime)
    · exact .inr (generatedLeftFactorAlternative state leftPrime)

abbrev FullFactorTerminalReachabilityAt
    (index : Nat) (indexInRange : 1 ≤ index) :=
  TerminalReachabilityAt
    (fullFactorRepairLaw index) (canonicalSplit index indexInRange)

abbrev FullFactorClosedResidualAt
    (index : Nat) (indexInRange : 1 ≤ index) :=
  ClosedReachabilityResidualAt
    (fullFactorRepairLaw index) (canonicalSplit index indexInRange)

inductive EffectiveFullFactorReachabilityDispositionAt
    (index : Nat) (indexInRange : 1 ≤ index) : Type
  | inhabited
      (reachability : FullFactorTerminalReachabilityAt index indexInRange)
      (fibre : EffectiveAdditiveFibreAt index)
      (fibre_eq : fibre = fibreOfTerminal reachability.terminal)
  | closed (residual : FullFactorClosedResidualAt index indexInRange)

/-- Framework-owned total full-factor reachability disposition. -/
noncomputable def generatedFullFactorReachabilityDisposition
    (index : Nat) (indexInRange : 1 ≤ index) :
    EffectiveFullFactorReachabilityDispositionAt index indexInRange := by
  cases SourceGeneratedFiniteEffectiveBranchingReachability.settle
      (fullFactorRepairLaw index) (canonicalSplit index indexInRange) with
  | inl reachability =>
      exact .inhabited reachability
        (fibreOfTerminal reachability.terminal) rfl
  | inr residual => exact .closed residual

/-- Same-occurrence rooted face.  Source target, complete factorization,
canonical start and the full-factor reachable image are all fixed by `index`.
-/
structure RootGeneratedFullFactorRepairReachabilityAt
    (index : Nat) (indexInRange : 1 ≤ index) : Type 7 where
  private mk ::
  occurrence : RootedAccountedUnfolding AdditiveCalculationPoint
  occurrence_eq : occurrence = evenTargetOccurrence index
  occurrenceRoot :
    occurrence.root.rootOccurrence = initialStep.generated.occurrence
  factorization : RootGeneratedEvenTargetFactorizationAt index
  factorization_eq : factorization = generatedEvenTargetFactorization index
  target : UnitHistory
  target_eq : target = evenTargetHistory index
  source : EffectiveSplitAt index
  source_eq : source = canonicalSplit index indexInRange
  sourceLanding :
    splitLeft source + splitRight source = target.cardinalShadow
  disposition : EffectiveFullFactorReachabilityDispositionAt index indexInRange
  disposition_eq :
    disposition = generatedFullFactorReachabilityDisposition index indexInRange

noncomputable def generatedFullFactorRepairReachabilityFace
    (index : Nat) (indexInRange : 1 ≤ index) :
    RootGeneratedFullFactorRepairReachabilityAt index indexInRange :=
  ⟨evenTargetOccurrence index, rfl,
    evenTargetOccurrence_root_is_exact index,
    generatedEvenTargetFactorization index, rfl,
    evenTargetHistory index, rfl,
    canonicalSplit index indexInRange, rfl,
    split_landing (canonicalSplit index indexInRange),
    generatedFullFactorReachabilityDisposition index indexInRange, rfl⟩

end
end CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
