import H0mework.Fock.HistoryConditional.InverseObservationHistoryIndex
import H0mework.Fock.InverseOptimal.Geometry
import H0mework.Realization.Operations.ObservationModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceCopyTimeModel
noncomputable section

theorem hilbert_step (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (SourceJointClockGraph.action value) (coordinate + 1) = hilbert value coordinate := by
  have paid := SourceGWordInverse.hilbert_recover 0 [.inl ⟨⟩]
    (SourceCompiledGWord.effect 0 [.inl ⟨⟩] value) coordinate
  rw [SourceGWordInverse.recover_effect] at paid
  rw [SourceCompiledGWord.effect_cons, SourceCompiledGWord.effect_nil, SourceCopyWordAffine.execute_original] at paid
  exact paid.symm

theorem hilbert_power (stage : Nat) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert ((SourceJointClockGraph.action.toLinearMap ^ stage) value) (coordinate + stage) = hilbert value coordinate := by
  induction stage with
  | zero => rfl
  | succ stage previous =>
    rw [pow_succ']
    change hilbert (SourceJointClockGraph.action ((SourceJointClockGraph.action.toLinearMap ^ stage) value))
      ((coordinate + stage) + 1) = _
    rw [hilbert_step, previous]

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
