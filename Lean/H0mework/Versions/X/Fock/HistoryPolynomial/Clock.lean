import H0mework.Versions.X.Fock.HistoryPolynomial.Relations
import H0mework.Versions.X.Fock.SourceHistoryClock.FrameInstalled

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Polynomial
noncomputable section

def clockRelation : Polynomial ℤ := (X - 1) ^ 2

private theorem clock_relation_expansion :
    clockRelation = monomial 2 1 + monomial 1 (-2) + monomial 0 1 := by
  simp only [clockRelation, ← C_mul_X_pow_eq_monomial]
  norm_num
  ring

theorem clock_relation_word : program clockRelation =
    Finsupp.single 2 1 + Finsupp.single 1 (-2) + Finsupp.single 0 1 := by
  rw [clock_relation_expansion, program_add, program_add, program_monomial, program_monomial, program_monomial]

theorem clock_relation_nonzero : clockRelation ≠ 0 := by
  intro same
  have coefficient := congrArg (fun p : Polynomial ℤ => p.coeff 2) same
  rw [clock_relation_expansion] at coefficient
  norm_num only [coeff_add, coeff_monomial, coeff_zero] at coefficient
  norm_num at coefficient

theorem clock_relation_invisible : clockRelation ∈ relationIdeal SourceClockModel.rawClock := by
  apply (ideal_is_source SourceClockModel.rawClock clockRelation).mpr
  intro step
  change SourceClockModel.clock ((SourceSuccessorBoundary.push ℤ ^ step) (program clockRelation)) = 0
  rw [SourceClockModel.clock_pow, clock_relation_word]
  simp [SourceClockModel.clock_single, SourceSuccessorBoundary.mass_single]

theorem clock_model_erases : SourceClockModel.projection (program clockRelation) = 0 := by
  have all := (ideal_is_source SourceClockModel.rawClock clockRelation).mp clock_relation_invisible
  have same := (model_fibre_iff nativeAction SourceClockModel.clock (program clockRelation) 0).mpr
    (by simpa only [map_zero] using all)
  simpa only [map_zero] using same

theorem prime_model_retains : projection nativeAction observation (program clockRelation) ≠ 0 := by
  intro vanished
  have original : program clockRelation = 0 := (original_model_fibre sourceOwner _ _).mp
    (vanished.trans (map_zero (projection nativeAction observation)).symm)
  apply clock_relation_nonzero
  apply program_injective
  have zero : program 0 = 0 := by unfold program; rw [map_zero]; rfl
  exact original.trans zero.symm

theorem prime_selector_recovers : selector sourceOwner 2 (program clockRelation) = 1 := by
  rw [original_selector_reads, clock_relation_expansion]
  norm_num only [coeff_add, coeff_monomial]
  norm_num

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
