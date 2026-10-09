import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.TerminalRead
import H0mework.Versions.R2.Arithmetic.GoldbachFourier.ClassicalBridge

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor
open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticClassicalGoldbachBridge
noncomputable section

def terminalSplitOfFibre {index : Nat} (fibre : EffectiveAdditiveFibreAt index) :
    Sigma fun state : EffectiveSplitAt index => PrimePairTerminalAt state := by
  let left := fibre.leftHistory.cardinalShadow
  let right := fibre.rightHistory.cardinalShadow
  have leftPrime : Nat.Prime left := fibre.left_isPrime
  have rightPrime : Nat.Prime right := fibre.right_isPrime
  have landing := congrArg UnitHistory.cardinalShadow fibre.lands
  rw [UnitHistory.cardinalShadow_parallel] at landing
  have leftFloor : 2 ≤ left := leftPrime.two_le
  have rightFloor : 2 ≤ right := rightPrime.two_le
  have bounded : left < repairTargetValue index + 1 := by
    dsimp only [repairTargetValue]
    omega
  let state : EffectiveSplitAt index :=
    ⟨⟨left, bounded⟩, by
      constructor
      · exact leftFloor
      · change 2 ≤ repairTargetValue index - left
        dsimp only [repairTargetValue]
        omega⟩
  refine ⟨state, ?_⟩
  constructor
  · exact leftPrime
  · change Nat.Prime (repairTargetValue index - left)
    have same : repairTargetValue index - left = right := by
      dsimp only [repairTargetValue]
      omega
    rw [same]
    exact rightPrime

theorem canonical_exhausted_fibre_empty
    (index : Nat) (indexInRange : 1 ≤ index)
    (history : ExhaustedAt (canonicalSplit index indexInRange)) :
    ¬ Nonempty (EffectiveAdditiveFibreAt index) := by
  rintro ⟨fibre⟩
  let terminal := terminalSplitOfFibre fibre
  exact (ExhaustedAt.canonical_exhausted_no_terminal index indexInRange
    history terminal.1) ⟨terminal.2⟩

end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
