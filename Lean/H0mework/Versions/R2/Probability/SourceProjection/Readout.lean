import H0mework.Versions.R2.Probability.SourceProjection.Field

/-! The actual current read is a generated coordinate of the universal source restriction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullProjection

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {State B : Type u} [AddCommGroup B]
variable (step : State → State) (read : State → B)

def readNow : Field step (sourcePoint (State := State)) →ₗ[ℤ] B :=
  (LinearMap.proj (0 : Fin 1)).comp
    ((stageRead (sourceAction step) (observation read) 0).comp (fieldMap step read))

theorem readNow_point (state : State) : readNow step read (fieldPoint step sourcePoint state) = read state := by
  change stageRead (sourceAction step) (observation read) 0
    (fieldMap step read (fieldPoint step sourcePoint state)) 0 = read state
  rw [fieldMap_point]
  exact (source_reads_stage (sourceAction step) (observation read) 0 (sourcePoint state) 0).trans
    (observation_point read state)

end
end SourceOwnedObservationHistory.FullProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
