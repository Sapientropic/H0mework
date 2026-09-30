import H0mework.Versions.X.Fock.SourceHistoryClock.PosteriorTasks

/-! Nonlinear source tasks are recovered pointwise without inventing a linear readout of the old clock model. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def sourceSquare (bound : Nat) (index : Fin (bound + 1)) : ℂ := task bound index ^ 2

theorem source_square_recovered (bound depth : Nat) :
    error (historyPMF bound) (observe bound depth) (sourceSquare bound)
      (optimalDecoder (historyPMF bound) (observe bound depth) (sourceSquare bound)) = 0 :=
  optimum_cost_zero bound depth (sourceSquare bound)

theorem future_model_second_difference (depth : Nat) :
    futureModel 2 depth 0 - (2 : ℤ) • futureModel 2 depth 1 + futureModel 2 depth 2 = 0 := by
  apply (SourceClockModel.model_ext_iff _ _).mpr
  constructor
  · simp only [map_add, map_sub, map_smul, map_zero, futureModel_source,
      SourceClockModel.Fock.mass_current, smul_eq_mul]
    norm_num
  · simp only [map_add, map_sub, map_smul, map_zero, futureModel_source,
      SourceClockModel.Fock.clock_current, runtimeAt_scanIndex, smul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
    ring

theorem no_linear_square_readout (depth : Nat) :
    ¬ ∃ read : SourceClockModel.Model →ₗ[ℤ] ℂ,
      ∀ index : Fin 3, read (futureModel 2 depth index) = sourceSquare 2 index := by
  rintro ⟨read, expresses⟩
  have relation := congrArg read (future_model_second_difference depth)
  simp only [map_add, map_sub, map_smul, map_zero, expresses] at relation
  norm_num [sourceSquare, task_source] at relation

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
