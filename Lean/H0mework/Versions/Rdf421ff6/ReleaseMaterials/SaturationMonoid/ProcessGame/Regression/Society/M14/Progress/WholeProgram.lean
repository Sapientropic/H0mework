import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Progress.PaidStep

/-!
# Canonical Society whole-program strict progress consumer

Consumes the original whole sink's registered finite root-law certificate.
It preserves that certificate's exact initial cycle and its root/whole-ledger/
next chain while deriving strict progress for every requested paid edge.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression

noncomputable section

open CanonicalSocietyProgress
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration

/-- The original whole sink supplies the actual cycle and root-law proof;
the subordinate progress consumer adds no root, current or receipt. -/
theorem CanonicalSocietyAt.registeredFiniteStrictCanonicalProgress
    {foundationHorizon : Nat} (society : CanonicalSocietyAt foundationHorizon)
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    Nonempty { initial : CycleAt oldVisit sourceIndex boundary //
      FiniteStrictCanonicalProgressAt initial fuel } := by
  obtain ⟨law⟩ := society.registeredFiniteCycleCanonicalRootLaw
    oldVisit sourceIndex boundary fuel
  exact ⟨⟨law.1, finiteStrictCanonicalProgressFromRootLaw law.1 fuel law.2⟩⟩

/-- Whole-sink synthesis of preservation and productive novelty, at every
exact caller Payment of every requested finite canonical prefix. -/
theorem canonicalSociety_registeredFiniteCycleStrictCanonicalProgress
    (foundationHorizon : Nat) (oldVisit : OldVisit)
    (sourceIndex boundary fuel : Nat) :
    Nonempty { initial : CycleAt oldVisit sourceIndex boundary //
      FiniteStrictCanonicalProgressAt initial fuel } :=
  (canonicalSociety foundationHorizon).registeredFiniteStrictCanonicalProgress
    oldVisit sourceIndex boundary fuel

end
end SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression

#print axioms SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_registeredFiniteCycleStrictCanonicalProgress
