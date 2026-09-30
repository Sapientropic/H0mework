import H0mework.Fock.HistoryConditional.NativeInverseSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

def horizon (program : Nat × Nat) : Nat := program.1 + program.2 - 1

def delay (program : Nat × Nat) (coordinate : Nat) : Nat := horizon program - coordinate % program.1

def sampleIndex (program : Nat × Nat) (coordinate : Nat) : Fin (horizon program + 1) :=
  ⟨delay program coordinate, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

theorem execute_delay (program : Nat × Nat) (positive : 0 < program.1) (coordinate : Nat) :
    SourceCopyWordAffine.execute program (coordinate / program.1) = coordinate + delay program coordinate := by
  have divided := Nat.mod_add_div coordinate program.1
  have small := Nat.mod_lt coordinate positive
  simp only [SourceCopyWordAffine.execute, delay, horizon, Nat.mul_add, Nat.mul_one]
  omega

theorem decode_delayed (program : Nat × Nat) (positive : 0 < program.1) (coordinate : Nat) :
    SourceNativeProgramInverse.decode program (coordinate + delay program coordinate) = some (coordinate / program.1) := by
  rw [← execute_delay program positive]
  exact SourceNativeProgramInverse.decode_execute program positive _

end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
