import H0mework.Realization.ObservationActions.DependentReadout
import H0mework.Probability.Empirical.ConditionalFormula

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent.Runtime

open SourceGeneratedEmpiricalHilbert SourceGeneratedScalarDifferentialResidual
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceGeneratedRuntimeHistoryProbability
open SourceConditionalTransfer
open scoped InnerProductSpace

noncomputable section

variable {N : WorldRelationNetwork.{0}} {process : SourceNativeLivingRootProcess N}
variable {B : Type} [AddCommGroup B] (read : process.State → B) (bound : Nat)
variable (cotest : ∀ runtime : LivingRuntimeState process, Space read runtime bound)

abbrev source (runtime : LivingRuntimeState process) :=
  sourceMap (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime

abbrev next (runtime : LivingRuntimeState process) :=
  nextCoimage (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime

abbrev reader (runtime : LivingRuntimeState process) :=
  coimageRead (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime

theorem next_source (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value) =
      canonicalResidual (source read bound cotest runtime.tick.next) (transfer read runtime bound value) :=
  next_coimage_source (C := fun r : LivingRuntimeState process => Space read r bound) (B := ℂ)
    (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime value

theorem next_read (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    reader read bound cotest runtime.tick.next
        (next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value)) =
      ⟪cotest runtime.tick.next, transfer read runtime bound value⟫_ℂ :=
  SourceGeneratedActionObservationHistory.Dependent.next_read
    (C := fun r : LivingRuntimeState process => Space read r bound) (B := ℂ)
    (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime value

theorem nextAtom_supported (runtime : LivingRuntimeState process) (index : Fin (bound + 1)) :
    nextAtom read runtime bound index ∈ (fieldPMF read runtime.tick.next bound).support := by
  apply (fieldPMF_support_iff read runtime.tick.next bound _).mpr
  exact ⟨index, (nextAtom_eq_next_sample read runtime bound index).symm⟩

theorem next_conditional (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    reader read bound cotest runtime.tick.next
        (next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value)) =
      ∑ index : Fin (bound + 1), (historyPMF bound index).toReal •
        ⟪cotest runtime.tick.next (nextAtom read runtime bound index),
          conditionalValue read runtime bound value (nextAtom read runtime bound index)
            (nextAtom_supported read bound runtime index)⟫_ℂ := by
  rw [next_read, inner_source_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [← nextAtom_eq_next_sample]
  rw [transfer_at_atom read runtime bound value _ (nextAtom_supported read bound runtime index)]

end
end SourceGeneratedActionObservationHistory.Dependent.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
