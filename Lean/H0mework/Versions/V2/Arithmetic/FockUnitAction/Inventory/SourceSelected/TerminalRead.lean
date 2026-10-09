import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Actor

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open ParticleWaveFockUnitChargeAction
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

private def appendFactorUnitPath {index : Nat} (indexInRange : 1 ≤ index)
    {start middle target : EffectiveSplitAt index}
    (front : GeneratedPathAt (factorUnitChargeLaw index indexInRange) start middle) :
    GeneratedPathAt (factorUnitChargeLaw index indexInRange) middle target →
      GeneratedPathAt (factorUnitChargeLaw index indexInRange) start target
  | .nil => front
  | .snoc prior action => (appendFactorUnitPath indexInRange front prior).snoc action

/-- The reached branch yields the original mixed factor/unit chronology and
the terminal at its actual endpoint. It does not manufacture a terminal. -/
def ReachedAt.terminalPath {index : Nat} (indexInRange : 1 ≤ index)
    {source : EffectiveSplitAt index} :
    ReachedAt source → TerminalReachabilityAt
      (factorUnitChargeLaw index indexInRange) source
  | .current terminal _classifierEq =>
      ⟨source, .nil, terminal⟩
  | .factor selected _inventoryEq _sourcePath _factorReceipt _factorReceiptEq =>
      ⟨selected.1.target,
        (GeneratedPathAt.nil : GeneratedPathAt
          (factorUnitChargeLaw index indexInRange) source source).snoc (.factor selected.1),
        selected.2⟩
  | .advance event tail =>
      let generated := ReachedAt.terminalPath indexInRange tail
      ⟨generated.state,
        appendFactorUnitPath indexInRange
          ((GeneratedPathAt.nil : GeneratedPathAt
            (factorUnitChargeLaw index indexInRange) source source).snoc (.unit event.unit))
          generated.path,
        generated.terminal⟩

/-- An exhausted result still carries the complete original mixed-law path
to its last inspected split, with no terminal inserted at the endpoint. -/
def ExhaustedAt.fullPath {index : Nat} (indexInRange : 1 ≤ index)
    {source : EffectiveSplitAt index} :
    ExhaustedAt source →
      Sigma fun target : EffectiveSplitAt index =>
        GeneratedPathAt (factorUnitChargeLaw index indexInRange) source target
  | .final _rightEq _factor _classifierEq _inventoryNone =>
      ⟨source, .nil⟩
  | .advance event tail =>
      let generated := ExhaustedAt.fullPath indexInRange tail
      ⟨generated.1,
        appendFactorUnitPath indexInRange
          ((GeneratedPathAt.nil : GeneratedPathAt
            (factorUnitChargeLaw index indexInRange) source source).snoc (.unit event.unit))
          generated.2⟩

theorem ExhaustedAt.fullPath_right_eq_two {index : Nat}
    (indexInRange : 1 ≤ index) {source : EffectiveSplitAt index}
    (history : ExhaustedAt source) :
    splitRight (history.fullPath indexInRange).1 = 2 := by
  induction history with
  | final rightEq _ _ _ => exact rightEq
  | advance event tail inductionHypothesis => exact inductionHypothesis

end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
