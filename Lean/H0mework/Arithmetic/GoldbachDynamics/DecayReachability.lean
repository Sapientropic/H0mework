import H0mework.Arithmetic.GoldbachDynamics.FactorEmission

/-!
# Combined repair/emission reachability

The exact effective split carrier is unchanged.  Its complete channel type
now inventories both shift repair and prime-factor emission.  The generic
branching kernel returns an actual prime-pair path or the complete reachable
sector closed under both decay mechanisms.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFullFactorDecayReachabilityProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticRoot
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

abbrev FullFactorDecayTerminalReachabilityAt
    (index : Nat) (indexInRange : 1 ≤ index) :=
  TerminalReachabilityAt
    (fullFactorDecayLaw index) (canonicalSplit index indexInRange)

abbrev FullFactorDecayClosedResidualAt
    (index : Nat) (indexInRange : 1 ≤ index) :=
  ClosedReachabilityResidualAt
    (fullFactorDecayLaw index) (canonicalSplit index indexInRange)

inductive EffectiveFullFactorDecayDispositionAt
    (index : Nat) (indexInRange : 1 ≤ index) : Type
  | inhabited
      (reachability :
        FullFactorDecayTerminalReachabilityAt index indexInRange)
      (fibre : EffectiveAdditiveFibreAt index)
      (fibre_eq : fibre = fibreOfTerminal reachability.terminal)
  | closed (residual : FullFactorDecayClosedResidualAt index indexInRange)

noncomputable def generatedFullFactorDecayDisposition
    (index : Nat) (indexInRange : 1 ≤ index) :
    EffectiveFullFactorDecayDispositionAt index indexInRange := by
  cases SourceGeneratedFiniteEffectiveBranchingReachability.settle
      (fullFactorDecayLaw index) (canonicalSplit index indexInRange) with
  | inl reachability =>
      exact .inhabited reachability
        (fibreOfTerminal reachability.terminal) rfl
  | inr residual => exact .closed residual

structure RootGeneratedFullFactorDecayReachabilityAt
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
  disposition : EffectiveFullFactorDecayDispositionAt index indexInRange
  disposition_eq : disposition =
    generatedFullFactorDecayDisposition index indexInRange

noncomputable def generatedFullFactorDecayReachabilityFace
    (index : Nat) (indexInRange : 1 ≤ index) :
    RootGeneratedFullFactorDecayReachabilityAt index indexInRange :=
  ⟨evenTargetOccurrence index, rfl,
    evenTargetOccurrence_root_is_exact index,
    generatedEvenTargetFactorization index, rfl,
    evenTargetHistory index, rfl,
    canonicalSplit index indexInRange, rfl,
    split_landing (canonicalSplit index indexInRange),
    generatedFullFactorDecayDisposition index indexInRange, rfl⟩

end
end CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
