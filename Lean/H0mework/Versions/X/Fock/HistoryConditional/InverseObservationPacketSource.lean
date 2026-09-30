import H0mework.Versions.X.Fock.HistoryConditional.InverseObservationHistoryModel
import H0mework.Versions.X.Fock.CopyGraph.TimeEnergySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationPacket

open SourceGeneratedActionWords SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def copyIndex (slope : Nat) : SourceCopyProgram.Index (slope - 1) :=
  ⟨slope - 1, by rw [SourceOwnedObservationHistory.Installed.runtime_bound]; omega⟩

theorem copy_scale (slope : Nat) (positive : 0 < slope) :
    SourceCopyProgram.scale (slope - 1) (copyIndex slope) = slope := by
  rw [SourceCopyProgram.scale_source]
  change slope - 1 + 1 = slope
  omega

theorem shifted_index (depth : Nat) (word : List (Fock.Letter depth)) (coordinate : Nat) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyWordAffine.execute program coordinate =
      SourceCopyProgram.indexAfter (program.1 - 1) (copyIndex program.1) coordinate + program.2 := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  have positive : 0 < program.1 := SourceCompiledWordOperator.slope_positive _
  change SourceCopyWordAffine.execute program coordinate =
    SourceCopyProgram.indexAfter (program.1 - 1) (copyIndex program.1) coordinate + program.2
  rw [SourceCopyProgram.index_source, copy_scale _ positive]
  have product : 0 < program.1 * (coordinate + 1) := Nat.mul_pos positive (Nat.succ_pos _)
  simp only [SourceCopyWordAffine.execute]
  rw [Nat.mul_comm (coordinate + 1)]
  omega

theorem delayed_observer (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceGWordInverse.recover depth word (time program.2 value) =
      SourceCopyGraph.recover (program.1 - 1) (copyIndex program.1) value := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply lp.ext
      funext coordinate
      change hilbert (SourceGWordInverse.recover depth word (time program.2 value)) coordinate =
        hilbert (SourceCopyGraph.recover (program.1 - 1) (copyIndex program.1) value) coordinate
      rw [SourceGWordInverse.hilbert_recover, shifted_index, time_hilbert_add, recover_hilbert]
    · change mass (SourceGWordInverse.recover depth word (time program.2 value)) = mass value
      rw [SourceGWordInverse.mass_recover, time_mass]
  · change (program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock (time program.2 value) -
      (program.2 : ℂ) * mass (time program.2 value)) =
      (SourceCopyProgram.scale (program.1 - 1) (copyIndex program.1) : ℂ)⁻¹ * SourceJointClockGraph.clock value
    rw [time_clock, time_mass, add_sub_cancel_right, copy_scale _ (SourceCompiledWordOperator.slope_positive _)]

def packet (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceJointClockGraph.Carrier →ₗ[ℂ]
      SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
        (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1) :=
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  LinearMap.pi fun phase => (SourceGWordInverse.recover depth word).toLinearMap.comp
    (time (program.2 + phase.val)).toLinearMap

theorem packet_source (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    packet depth word value = SourceCopyTimeModel.phases (program.1 - 1) (copyIndex program.1) value := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  funext phase
  change SourceGWordInverse.recover depth word (time (program.2 + phase.val) value) = _
  have compose : time (program.2 + phase.val) value = time program.2 (time phase.val value) := by
    simp only [time, pow_add, mul_apply_eq_comp]
  rw [compose, delayed_observer, SourceCopyTimeModel.phase_source]

theorem native_sample (depth : Nat) (word : List (Fock.Letter depth)) (runtime : LivingRuntimeState process)
    (phase : Fin ((copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1).val + 1)) :
    packet depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) phase =
      SourceGWordInverse.recover depth word
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point
          (runtime.advance ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 + phase.val))))) := by
  change SourceGWordInverse.recover depth word (time _ _) = _
  rw [time_native]

end
end SourceInverseObservationPacket
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
