import H0mework.Versions.X.Fock.PrimeField.CompletionBoundary

/-! One original finite source lift carries the old boundary and unit equations into the complete Field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

theorem coefficient_zero (owner : GlobalParentOwner) (value : Field) :
    coefficient owner 0 value = mass value - primitive owner 0 value := by
  obtain ⟨word, agrees⟩ := finite_source_reads value (delay owner 0 + 1)
  let point : Field := sourceMap nativeAction observation word
  have reads (stage : Nat) (inside : stage ≤ delay owner 0 + 1) : read stage point = read stage value := agrees stage inside
  have source := source_zero word
  rw [← coefficient_source owner 0 word, ← mass_source word, ← primitive_source owner 0 word] at source
  change coefficient owner 0 point = mass point - primitive owner 0 point at source
  unfold coefficient mass primitive at source ⊢
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at source ⊢
  rw [reads _ le_rfl, reads (delay owner 0) (by omega), reads 0 (by omega)] at source
  exact source

theorem coefficient_successor (owner : GlobalParentOwner) (value : Field) (index : Nat) :
    coefficient owner (index + 1) value = primitive owner index value - primitive owner (index + 1) value := by
  let bound := max (delay owner index) (delay owner (index + 1) + 1)
  obtain ⟨word, agrees⟩ := finite_source_reads value bound
  let point : Field := sourceMap nativeAction observation word
  have reads (stage : Nat) (inside : stage ≤ bound) : read stage point = read stage value := agrees stage inside
  have first : delay owner index ≤ bound := Nat.le_max_left _ _
  have next : delay owner (index + 1) + 1 ≤ bound := Nat.le_max_right _ _
  have source := source_successor word index
  rw [← coefficient_source owner (index + 1) word, ← primitive_source owner index word,
    ← primitive_source owner (index + 1) word] at source
  change coefficient owner (index + 1) point = primitive owner index point - primitive owner (index + 1) point at source
  unfold coefficient primitive at source ⊢
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at source ⊢
  rw [reads _ next, reads (delay owner (index + 1)) (by omega), reads _ first] at source
  exact source

theorem source_row_on_completion (owner : GlobalParentOwner) (value : Field) (prime : Nat.Primes) (stage : Nat) :
    primeRead prime (read stage value) =
      if cut prime ≤ stage then mass value else primitive owner (cut prime - stage - 1) value := by
  let index := cut prime - stage - 1
  let bound := max stage (delay owner index)
  obtain ⟨word, agrees⟩ := finite_source_reads value bound
  let point : Field := sourceMap nativeAction observation word
  have reads (time : Nat) (inside : time ≤ bound) : read time point = read time value := agrees time inside
  have atStage : stage ≤ bound := Nat.le_max_left _ _
  have atPrimitive : delay owner index ≤ bound := Nat.le_max_right _ _
  have source := LinearMap.congr_fun (source_row_is_prime_read prime stage) word
  change sourceRow prime stage word = primeRead prime (observation ((nativeAction ^ stage) word)) at source
  rw [← read_source, agrees _ atStage] at source
  unfold sourceRow at source
  by_cases early : cut prime ≤ stage
  · rw [if_pos early] at source ⊢
    rw [← mass_source word] at source
    change mass point = primeRead prime (read stage value) at source
    unfold mass at source
    simp only [LinearMap.comp_apply] at source
    rw [reads 0 (Nat.zero_le _)] at source
    exact source.symm
  · rw [if_neg early] at source ⊢
    change SourceSuccessorBoundary.certificate ℤ word index = _ at source
    rw [← primitive_source owner index word] at source
    change primitive owner index point = primeRead prime (read stage value) at source
    unfold primitive at source
    simp only [LinearMap.comp_apply] at source
    rw [reads _ atPrimitive] at source
    exact source.symm

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
