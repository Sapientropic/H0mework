import H0mework.Fock.HistoryConditional.OperatorRecurrenceInstance
import H0mework.Fock.HistoryConditional.NativeInverseG

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def hiddenIndex (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat) : Nat :=
  SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) - length - 1

def hidden (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat) : SourceJointClockGraph.Carrier :=
  SourceGWordInverse.residual depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative
    (SourceOperationNative.statePoint process (hiddenIndex depth word length))))

theorem image_floor (depth : Nat) (word : List (Fock.Letter depth)) (coordinate : Nat) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceInverseObservationHistory.horizon program ≤ SourceCopyWordAffine.execute program coordinate := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  have larger : program.1 ≤ program.1 * (coordinate + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change program.1 + program.2 - 1 ≤ program.1 * (coordinate + 1) + program.2 - 1
  omega

theorem hidden_outside (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (hiddenIndex depth word length) = none := by
  apply (SourceNativeProgramInverse.decode_none_iff _ (SourceCompiledWordOperator.slope_positive _) _).mpr
  rintro ⟨coordinate, same⟩
  have floor := image_floor depth word coordinate
  dsimp only at floor
  rw [same] at floor
  dsimp only [hiddenIndex] at floor
  omega

theorem hidden_balance (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    let point := SourceJointClockGraph.read (SourceClockComplex.ofNative
      (SourceOperationNative.statePoint process (hiddenIndex depth word length)))
    hidden depth word length + SourceCopyGraph.axes (mass point) (SourceJointClockGraph.clock point) = point := by
  have paid := SourceGWordInverse.residual_native_moments depth word
    (SourceOperationNative.statePoint process (hiddenIndex depth word length))
  have source : SourceCompiledWordOperator.residual depth word
      (SourceOperationNative.statePoint process (hiddenIndex depth word length)) =
      SourceOperationNative.statePoint process (hiddenIndex depth word length) :=
    SourceNativeProgramInverse.raw_outside depth word _ (hidden_outside depth word length shorter)
  rw [source] at paid
  exact paid

theorem hidden_mass (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    mass (hidden depth word length) = 0 := by
  have paid := congrArg mass (hidden_balance depth word length shorter)
  simp only [mass, map_add] at paid
  change mass (hidden depth word length) + _ = _ at paid
  exact add_right_cancel (paid.trans (zero_add _).symm)

theorem hidden_clock (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    SourceJointClockGraph.clock (hidden depth word length) = 0 := by
  have paid := congrArg SourceJointClockGraph.clock (hidden_balance depth word length shorter)
  rw [map_add] at paid
  change SourceJointClockGraph.clock (hidden depth word length) + _ = _ at paid
  exact add_right_cancel (paid.trans (zero_add _).symm)

theorem hidden_coordinate (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))
    (coordinate : Nat) :
    hilbert (hidden depth word length) coordinate = if hiddenIndex depth word length = coordinate then 1 else 0 := by
  have paid := congrArg (fun value : SourceJointClockGraph.Carrier => hilbert value coordinate)
    (hidden_balance depth word length shorter)
  simp only [hilbert, map_add, lp.coeFn_add, Pi.add_apply] at paid
  change hilbert (hidden depth word length) coordinate + 0 = SourceSuccessorBoundary.readWord
    (SourceClockComplex.ofNative (SourceOperationNative.statePoint process (hiddenIndex depth word length))) coordinate at paid
  rw [add_zero, SourceCopyGraph.native_hilbert, SourceOwnedObservationHistory.SourceShift.wordRead_coordinate] at paid
  simpa only [SourceOperationNative.statePoint, Finsupp.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero] using paid

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
