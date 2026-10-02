import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.FactorOrbit
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root

/-!
# Existing-unit fixed-target transfer kernel

One already-present right unit is exposed as `.next remainder` and transferred
to the left history.  Structural parallel equality proves that the same whole
occurrence is preserved: no unit is generated, cloned, or silently discarded.
The canonical native write is only the left-coordinate readback.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockUnitChargeAction

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticRoot

noncomputable section

/-! ## Same-whole existing-unit transfer -/

/-- Moving the exposed outer right occurrence to the left is an equality of
actual unary histories, proved before any cardinal readout. -/
theorem UnitHistory.parallel_next_transfer
    (left remainder : UnitHistory) :
    left.parallel (UnitHistory.next remainder) =
      (UnitHistory.next left).parallel remainder := by
  induction remainder with
  | empty => rfl
  | next remainder inductionHypothesis =>
      exact congrArg UnitHistory.next inductionHypothesis

/-- Positive generated history exposes its outer occurrence and generated
remainder structurally. -/
theorem UnitHistory.generate_eq_next_pred {count : Nat} (positive : 0 < count) :
    UnitHistory.generate count = .next (UnitHistory.generate (count - 1)) := by
  cases count with
  | zero => omega
  | succ count => simp [UnitHistory.generate]

/-- Generated parallel histories compute addition structurally; no cardinal
extensionality is used to install the source whole. -/
theorem UnitHistory.generate_parallel_generate (left right : Nat) :
    (UnitHistory.generate left).parallel (UnitHistory.generate right) =
      UnitHistory.generate (left + right) := by
  induction right with
  | zero => simp [UnitHistory.generate, UnitHistory.parallel]
  | succ right inductionHypothesis =>
      change UnitHistory.next
          ((UnitHistory.generate left).parallel (UnitHistory.generate right)) =
        UnitHistory.generate (left + (right + 1))
      rw [inductionHypothesis, Nat.add_succ]
      rfl

/-- One existing outer unit is reclassified from the right face to the left
face.  The right history itself is an index, so the receipt cannot silently
replace it by a merely equicardinal history. -/
structure ExistingUnitTransferAt
    (sourceLeft sourceRight : UnitHistory) : Type where
  private mk ::
  remainder : UnitHistory
  sourceRight_eq : sourceRight = .next remainder

namespace ExistingUnitTransferAt

def targetLeft {sourceLeft sourceRight : UnitHistory}
    (_transfer : ExistingUnitTransferAt sourceLeft sourceRight) : UnitHistory :=
  .next sourceLeft

def targetRight {sourceLeft sourceRight : UnitHistory}
    (transfer : ExistingUnitTransferAt sourceLeft sourceRight) : UnitHistory :=
  transfer.remainder

/-- The same exposed constructor occurs on opposite sides of the parallel
partition; this equality is structural and uses no cardinal collapse. -/
theorem whole_eq {sourceLeft sourceRight : UnitHistory}
    (transfer : ExistingUnitTransferAt sourceLeft sourceRight) :
    sourceLeft.parallel sourceRight =
      transfer.targetLeft.parallel transfer.targetRight := by
  rcases transfer with ⟨remainder, rfl⟩
  exact UnitHistory.parallel_next_transfer sourceLeft remainder

theorem cardinal_left {sourceLeft sourceRight : UnitHistory}
    (transfer : ExistingUnitTransferAt sourceLeft sourceRight) :
    transfer.targetLeft.cardinalShadow = sourceLeft.cardinalShadow + 1 :=
  rfl

theorem cardinal_right {sourceLeft sourceRight : UnitHistory}
    (transfer : ExistingUnitTransferAt sourceLeft sourceRight) :
    transfer.targetRight.cardinalShadow + 1 = sourceRight.cardinalShadow := by
  rcases transfer with ⟨remainder, rfl⟩
  rfl

end ExistingUnitTransferAt

/-- The positive generated right face exposes its actual outer constructor;
the predecessor is not supplied by a caller. -/
def generateExistingUnitTransfer
    (sourceLeft : UnitHistory) (rightCount : Nat) (positive : 0 < rightCount) :
    ExistingUnitTransferAt sourceLeft (UnitHistory.generate rightCount) :=
  { remainder := UnitHistory.generate (rightCount - 1)
    sourceRight_eq := UnitHistory.generate_eq_next_pred positive }

def generateExistingUnitTransferAt
    (sourceLeft sourceRight : UnitHistory) (rightCount : Nat)
    (sourceRight_eq : sourceRight = UnitHistory.generate rightCount)
    (positive : 0 < rightCount) :
    ExistingUnitTransferAt sourceLeft sourceRight := by
  subst sourceRight
  exact generateExistingUnitTransfer sourceLeft rightCount positive

/-- One unit of charge moves from right to left.  Its left-coordinate update
is exactly the canonical root's native unit write, not a free numeric shift. -/
def unitChargeTarget {index : Nat} {source : EffectiveSplitAt index}
    (_rightRoom : 3 ≤ splitRight source) : EffectiveSplitAt index := by
  have sourceLanding := split_landing source
  have leftFloor := splitLeft_atLeastTwo source
  have leftLeTarget : splitLeft source + 1 ≤ repairTargetValue index := by omega
  exact
    ⟨⟨splitLeft source + 1, Nat.lt_succ_of_le leftLeTarget⟩,
      leftFloor.trans (Nat.le_add_right _ _), by
        change 2 ≤ repairTargetValue index - (splitLeft source + 1)
        omega⟩

@[simp] theorem unitChargeTarget_left {index : Nat}
    {source : EffectiveSplitAt index} (rightRoom : 3 ≤ splitRight source) :
    splitLeft (unitChargeTarget rightRoom) = splitLeft source + 1 :=
  rfl

@[simp] theorem unitChargeTarget_right {index : Nat}
    {source : EffectiveSplitAt index} (rightRoom : 3 ≤ splitRight source) :
    splitRight (unitChargeTarget rightRoom) = splitRight source - 1 := by
  have sourceLanding := split_landing source
  have targetLanding := split_landing (unitChargeTarget rightRoom)
  rw [unitChargeTarget_left] at targetLanding
  omega

/-- Every effective split is a structural parallel readout of the generated
fixed whole. -/
theorem generatedSplitWhole_eq_evenTarget {index : Nat}
    (state : EffectiveSplitAt index) :
    (UnitHistory.generate (splitLeft state)).parallel
        (UnitHistory.generate (splitRight state)) = evenTargetHistory index := by
  rw [UnitHistory.generate_parallel_generate, split_landing]
  unfold repairTargetValue
  rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]

structure UnitChargeActionAt {index : Nat}
    (source : EffectiveSplitAt index) : Type where
  private mk ::
  rightRoom : 3 ≤ splitRight source
  target : EffectiveSplitAt index
  target_eq : target = unitChargeTarget rightRoom
  sourceLeftHistory : UnitHistory
  sourceLeftHistory_eq : sourceLeftHistory = UnitHistory.generate (splitLeft source)
  sourceRightHistory : UnitHistory
  sourceRightHistory_eq : sourceRightHistory = UnitHistory.generate (splitRight source)
  transfer : ExistingUnitTransferAt sourceLeftHistory sourceRightHistory
  transfer_eq : transfer =
    generateExistingUnitTransferAt sourceLeftHistory sourceRightHistory
      (splitRight source) sourceRightHistory_eq (by omega)
  targetLeftHistory : UnitHistory
  targetLeftHistory_eq : targetLeftHistory = transfer.targetLeft
  targetLeftHistory_generated :
    targetLeftHistory = UnitHistory.generate (splitLeft target)
  targetRightHistory : UnitHistory
  targetRightHistory_eq : targetRightHistory = transfer.targetRight
  rootWrite : CanonicalUnitArithmeticRoot.NativeWriteAt sourceLeftHistory
  rootWrite_eq : rootWrite = CanonicalUnitArithmeticRoot.nativeWriteAt sourceLeftHistory
  rootWriteBackEquation : rootWrite.wholeWriteBack = sourceLeftHistory
  rootWrite_target_readback : rootWrite.target = targetLeftHistory
  leftActionEquation : splitLeft target = rootWrite.target.cardinalShadow
  rightWriteEquation : splitRight target + 1 = splitRight source
  targetRightHistory_generated :
    targetRightHistory = UnitHistory.generate (splitRight target)
  sourceWholeEquation :
    sourceLeftHistory.parallel sourceRightHistory = evenTargetHistory index
  targetWholeEquation :
    targetLeftHistory.parallel targetRightHistory = evenTargetHistory index

def generateUnitChargeAction {index : Nat} (source : EffectiveSplitAt index)
    (rightRoom : 3 ≤ splitRight source) : UnitChargeActionAt source := by
  let sourceLeftHistory := UnitHistory.generate (splitLeft source)
  let sourceRightHistory := UnitHistory.generate (splitRight source)
  let transfer := generateExistingUnitTransferAt sourceLeftHistory
    sourceRightHistory (splitRight source) rfl (by omega)
  let targetLeftHistory := transfer.targetLeft
  let targetRightHistory := transfer.targetRight
  let rootWrite := CanonicalUnitArithmeticRoot.nativeWriteAt sourceLeftHistory
  let target := unitChargeTarget rightRoom
  have rootWriteTargetReadback : rootWrite.target = targetLeftHistory := by
    change CanonicalUnitArithmeticRoot.next sourceLeftHistory =
      UnitHistory.next sourceLeftHistory
    exact CanonicalUnitArithmeticRoot.next_eq_next sourceLeftHistory
  have leftActionEquation : splitLeft target = rootWrite.target.cardinalShadow := by
    rw [unitChargeTarget_left]
    change splitLeft source + 1 =
      (CanonicalUnitArithmeticRoot.nativeWriteAt
        (UnitHistory.generate (splitLeft source))).target.cardinalShadow
    rw [CanonicalUnitArithmeticRoot.nativeWriteAt_target,
      CanonicalUnitArithmeticRoot.next_eq_next]
    simp only [UnitHistory.cardinalShadow,
      UnitHistory.cardinalShadow_generate]
  have targetLeftHistoryGenerated :
      targetLeftHistory = UnitHistory.generate (splitLeft target) := by
    change UnitHistory.next (UnitHistory.generate (splitLeft source)) =
      UnitHistory.generate (splitLeft (unitChargeTarget rightRoom))
    rw [unitChargeTarget_left]
    rfl
  have targetRightHistoryGenerated :
      targetRightHistory = UnitHistory.generate (splitRight target) := by
    change UnitHistory.generate (splitRight source - 1) =
      UnitHistory.generate (splitRight (unitChargeTarget rightRoom))
    rw [unitChargeTarget_right]
  have sourceWholeEquation :
      sourceLeftHistory.parallel sourceRightHistory = evenTargetHistory index := by
    exact generatedSplitWhole_eq_evenTarget source
  exact
    { rightRoom := rightRoom
      sourceLeftHistory := sourceLeftHistory
      sourceLeftHistory_eq := rfl
      sourceRightHistory := sourceRightHistory
      sourceRightHistory_eq := rfl
      transfer := transfer
      transfer_eq := rfl
      targetLeftHistory := targetLeftHistory
      targetLeftHistory_eq := rfl
      targetLeftHistory_generated := targetLeftHistoryGenerated
      targetRightHistory := targetRightHistory
      targetRightHistory_eq := rfl
      rootWrite := rootWrite
      rootWrite_eq := rfl
      rootWriteBackEquation :=
        CanonicalUnitArithmeticRoot.nativeWriteAt_wholeWriteBack _
      rootWrite_target_readback := rootWriteTargetReadback
      target := target
      target_eq := rfl
      leftActionEquation := leftActionEquation
      rightWriteEquation := by
        rw [unitChargeTarget_right]
        omega
      targetRightHistory_generated := targetRightHistoryGenerated
      sourceWholeEquation := sourceWholeEquation
      targetWholeEquation := by
        exact transfer.whole_eq.symm.trans sourceWholeEquation }

end
end ParticleWaveFockUnitChargeAction
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
