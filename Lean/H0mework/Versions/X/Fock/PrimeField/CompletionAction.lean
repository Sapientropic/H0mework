import H0mework.Versions.X.Fock.PrimeField.CompletionRecovery

/-! The original complete Field action generates the coefficient shift while retaining the original mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

theorem read_advance (value : Field) (stage : Nat) :
    read stage (fieldAction (process := process) rawField value) = read (stage + 1) value :=
  congrFun (endomorphism_reads_dropFirst nativeAction observation stage value) (Fin.last stage)

theorem mass_advance (owner : GlobalParentOwner) (value : Field) :
    mass (fieldAction (process := process) rawField value) = mass value := by
  unfold mass
  simp only [LinearMap.comp_apply]
  rw [read_advance, source_row_on_completion owner]
  exact if_pos (by decide)

theorem primitive_zero_advance (owner : GlobalParentOwner) (value : Field) :
    primitive owner 0 (fieldAction (process := process) rawField value) = mass value := by
  change primeRead (selectedPrime owner 0) (read (delay owner 0) (fieldAction (process := process) rawField value)) = _
  rw [read_advance, source_row_on_completion owner, if_pos (by rw [selected_cut]; omega)]

theorem primitive_successor_advance (owner : GlobalParentOwner) (value : Field) (index : Nat) :
    primitive owner (index + 1) (fieldAction (process := process) rawField value) = primitive owner index value := by
  change primeRead (selectedPrime owner (index + 1))
    (read (delay owner (index + 1)) (fieldAction (process := process) rawField value)) = _
  rw [read_advance, source_row_on_completion owner, if_neg (by rw [selected_cut]; omega)]
  have position : cut (selectedPrime owner (index + 1)) - (delay owner (index + 1) + 1) - 1 = index := by
    rw [selected_cut]
    omega
  rw [position]

theorem coefficient_zero_advance (owner : GlobalParentOwner) (value : Field) :
    coefficient owner 0 (fieldAction (process := process) rawField value) = 0 := by
  rw [coefficient_zero, mass_advance owner, primitive_zero_advance, sub_self]

theorem coefficient_successor_advance (owner : GlobalParentOwner) (value : Field) (index : Nat) :
    coefficient owner (index + 1) (fieldAction (process := process) rawField value) = coefficient owner index value := by
  rw [coefficient_successor, primitive_successor_advance]
  cases index with
  | zero => rw [primitive_zero_advance, coefficient_zero]
  | succ index => rw [primitive_successor_advance, coefficient_successor]

theorem field_action_injective (owner : GlobalParentOwner) : Function.Injective (fieldAction (process := process) rawField) := by
  intro left right same
  apply coefficients_injective owner
  funext index
  change coefficient owner index left = coefficient owner index right
  have next := congrArg (coefficient owner (index + 1)) same
  rw [coefficient_successor_advance, coefficient_successor_advance] at next
  exact next

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
