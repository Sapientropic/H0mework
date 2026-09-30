import H0mework.Fock.InverseBirth.Minimum
import H0mework.Fock.HistoryConditional.NativeInverseG

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem point_outside_cost (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat) :
    ‖SourceGWordInverse.residual depth word
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single target 1)))‖ ^ 2 =
      if SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target = none then 1 else 0 := by
  have paid := SourceGWordInverse.residual_native_moments depth word (Finsupp.single target 1)
  rw [SourceNativeProgramInverse.raw_residual] at paid
  cases computed : SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
  | none =>
    simp only [ite_true]
    rw [computed] at paid
    have same := (eq_sub_iff_add_eq).mpr paid
    rw [same, SourceInverseDistributionLoss.norm_sub_axes]
    change ‖SourceSuccessorBoundary.readWord (SourceClockComplex.ofNative (Finsupp.single target 1))‖ ^ 2 = 1
    rw [SourceClockComplex.ofNative_single, SourceSuccessorBoundary.readWord_single]
    simp [SourceOwnedObservationHistory.SourceShift.basis]
  | some state =>
    simp only [Option.some_ne_none, if_false]
    rw [computed] at paid
    simp only [map_zero] at paid
    change SourceGWordInverse.residual depth word
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single target 1))) + 0 = 0 at paid
    rw [add_zero] at paid
    rw [paid, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem born_cost (bound depth : Nat) (word : List (Fock.Letter depth)) :
    ‖SourceGWordInverse.residual depth word (SourceConditionalInventory.born bound)‖ ^ 2 =
      if SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (bound + 2) = none then 1 else 0 := by
  rw [← SourceConditionalWordStream.born_read, SourceConditionalWordStream.bornWord, SourceConditionalWordStream.source_single]
  have paid := point_outside_cost depth word (bound + 2)
  rw [SourceClockComplex.ofNative_single, Int.cast_one] at paid
  exact paid

theorem source_increment {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    increment runtime depth word read =
      (if SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (inventoryBound runtime + 2) = none then 1 else 0) +
      ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 : ℝ) /
        ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 + 1) *
        ‖project depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
          decoder runtime depth word read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  rw [increment, born_cost]

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
