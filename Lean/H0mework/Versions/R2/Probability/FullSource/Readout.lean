import H0mework.Versions.R2.Probability.FullSource.Word
import H0mework.Versions.R2.Probability.SourceProjection.Readout

/-! Every reader consumes the same recovered source word without selecting a native state. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullWord

open SourceGeneratedActionObservationHistory FullProjection

noncomputable section

universe u

variable {State B : Type u} [AddCommGroup B]
variable (step : State → State)

theorem word_point (state : State) : word step (fieldPoint step sourcePoint state) = sourcePoint state :=
  word_source step (sourcePoint state)

theorem readNow_word (read : State → B) (value : Field step (sourcePoint (State := State))) :
    readNow step read value = observation read (word step value) := by
  rw [← source_word step value]
  change stageRead (sourceAction step) (observation read) 0
    (fieldMap step read (sourceMap (sourceAction step) (observation sourcePoint) (word step value))) 0 = _
  rw [fieldMap_source, source_reads_stage, word_source]
  rfl

theorem zero_not_native (state : State) : (0 : Field step (sourcePoint (State := State))) ≠
    fieldPoint step sourcePoint state := by
  intro same
  have impossible := congrArg (word step) same
  rw [map_zero, word_point] at impossible
  exact (Finsupp.single_ne_zero.mpr (one_ne_zero : (1 : ℤ) ≠ 0)) impossible.symm

end
end SourceOwnedObservationHistory.FullWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
