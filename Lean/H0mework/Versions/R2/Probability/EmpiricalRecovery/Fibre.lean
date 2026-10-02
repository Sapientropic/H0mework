import H0mework.Versions.R2.Probability.Empirical.Error

/-! Zero residual is exactly constancy on every actual next fibre and existence of an exact raw decoder. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory
open scoped Classical

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

theorem zero_residual_recovers (value : Space read runtime bound) (vanished : residual read runtime bound value = 0)
    (index : Fin (bound + 1)) :
    value (fieldSample read runtime bound index) = transfer read runtime bound value (nextAtom read runtime bound index) := by
  have source := pullback_transfer_add_residual read runtime bound value
  rw [vanished, add_zero] at source
  have observed := congrArg (fun current : Space read runtime bound => current (fieldSample read runtime bound index)) source
  rw [pullback_at_sample] at observed
  exact observed.symm

theorem zero_residual_iff_fibre (value : Space read runtime bound) :
    residual read runtime bound value = 0 ↔
      ∀ first second : Fin (bound + 1), nextAtom read runtime bound first = nextAtom read runtime bound second →
        value (fieldSample read runtime bound first) = value (fieldSample read runtime bound second) := by
  constructor
  · intro vanished first second same
    rw [zero_residual_recovers read runtime bound value vanished first,
      zero_residual_recovers read runtime bound value vanished second, same]
  · intro constant
    have recovered (index : Fin (bound + 1)) :
        transfer read runtime bound value (nextAtom read runtime bound index) = value (fieldSample read runtime bound index) := by
      have supported : nextAtom read runtime bound index ∈ (fieldPMF read runtime.tick.next bound).support :=
        (fieldPMF_support_iff read runtime.tick.next bound _).mpr
          ⟨index, (nextAtom_eq_next_sample read runtime bound index).symm⟩
      rw [transfer_at_atom read runtime bound value _ supported, conditionalValue]
      calc
        _ = ∑ other : Fin (bound + 1),
            (conditionalIndices read runtime bound (nextAtom read runtime bound index) supported other).toReal •
              value (fieldSample read runtime bound index) := by
          apply Finset.sum_congr rfl
          intro other _
          by_cases member : other ∈ (conditionalIndices read runtime bound (nextAtom read runtime bound index) supported).support
          · exact congrArg ((conditionalIndices read runtime bound (nextAtom read runtime bound index) supported other).toReal • ·)
              (constant other index ((conditionalIndices_support_iff read runtime bound _ supported other).mp member))
          · have zero := ((conditionalIndices read runtime bound (nextAtom read runtime bound index) supported).apply_eq_zero_iff other).mpr member
            simp only [zero, ENNReal.toReal_zero, zero_smul]
        _ = _ := by
          rw [← PMF.integral_eq_sum]
          simp
    have errorZero : sourceError read runtime bound value (fun atom => transfer read runtime bound value atom) = 0 := by
      unfold sourceError
      apply Finset.sum_eq_zero
      intro index _
      simp only [recovered, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    rw [transfer_attains] at errorZero
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (residual read runtime bound value)]

theorem zero_residual_iff_decoder (value : Space read runtime bound) :
    residual read runtime bound value = 0 ↔
      ∃ decoder : Field read → ℂ, ∀ index : Fin (bound + 1),
        value (fieldSample read runtime bound index) = decoder (nextAtom read runtime bound index) := by
  constructor
  · intro vanished
    exact ⟨fun atom => transfer read runtime bound value atom, zero_residual_recovers read runtime bound value vanished⟩
  · rintro ⟨decoder, recovers⟩
    apply (zero_residual_iff_fibre read runtime bound value).mpr
    intro first second same
    exact (recovers first).trans ((congrArg decoder same).trans (recovers second).symm)

end
end SourceConditionalRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
