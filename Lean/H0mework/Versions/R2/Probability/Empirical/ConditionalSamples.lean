import H0mework.Versions.R2.Probability.Empirical.Transfer
import H0mework.Versions.R2.Realization.HistoryTopology.Compactness
import H0mework.Versions.R2.Probability.Runtime.Conditional

/-! The existing empirical adjoint is read on the indices of its own current and next samples. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

def fieldSample (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) : Field read :=
  fieldPoint read (sample runtime bound index)

def nextAtom (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) : Field read :=
  fieldAction read (fieldSample read runtime bound index)

theorem fieldPMF_from_indices (runtime : LivingRuntimeState process) (bound : Nat) :
    fieldPMF read runtime bound = (historyPMF bound).map (fieldSample read runtime bound) :=
  PMF.map_comp (sample runtime bound) (historyPMF bound) (fieldPoint read)

theorem nextPMF_from_indices (runtime : LivingRuntimeState process) (bound : Nat) :
    fieldPMF read runtime.tick.next bound = (historyPMF bound).map (nextAtom read runtime bound) := by
  rw [← fieldPMF_action, fieldPMF_from_indices, PMF.map_comp]
  rfl

theorem sample_mass_ne_zero (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    (empirical read runtime bound).toMeasure {fieldSample read runtime bound index} ≠ 0 := by
  change (fieldPMF read runtime bound).toMeasure _ ≠ 0
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact (fieldPMF_support_iff read runtime bound _).mpr ⟨index, rfl⟩

theorem ae_at_sample (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1))
    {predicate : Field read → Prop}
    (proof : ∀ᵐ point ∂(empirical read runtime bound).toMeasure, predicate point) :
    predicate (fieldSample read runtime bound index) := by
  obtain ⟨point, member, holds⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (sample_mass_ne_zero read runtime bound index) (ae_restrict_of_ae proof)
  exact Set.mem_singleton_iff.mp member ▸ holds

theorem pullback_at_sample (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Space read runtime.tick.next bound) (index : Fin (bound + 1)) :
    pullback read runtime bound value (fieldSample read runtime bound index) =
      value (nextAtom read runtime bound index) :=
  ae_at_sample read runtime bound index (pullback_ae read runtime bound value)

theorem transfer_cotest (runtime : LivingRuntimeState process) (bound : Nat)
    (test : Space read runtime.tick.next bound) (value : Space read runtime bound) :
    ⟪test, transfer read runtime bound value⟫_ℂ = ⟪pullback read runtime bound test, value⟫_ℂ :=
  (pullback read runtime bound).toContinuousLinearMap.adjoint_inner_right test value

theorem integral_source_sum (runtime : LivingRuntimeState process) (bound : Nat)
    (function : Field read → ℂ)
    (measurable : AEStronglyMeasurable function (empirical read runtime bound).toMeasure) :
    ∫ point, function point ∂(empirical read runtime bound).toMeasure =
      ∑ index : Fin (bound + 1), (historyPMF bound index).toReal • function (fieldSample read runtime bound index) := by
  change AEStronglyMeasurable function (fieldPMF read runtime bound).toMeasure at measurable
  change (∫ point, function point ∂(fieldPMF read runtime bound).toMeasure) = _
  rw [fieldPMF_from_indices,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _)] at measurable ⊢
  rw [integral_map (measurable_of_finite _).aemeasurable measurable, PMF.integral_eq_sum]

theorem inner_source_sum (runtime : LivingRuntimeState process) (bound : Nat)
    (left right : Space read runtime bound) :
    ⟪left, right⟫_ℂ = ∑ index : Fin (bound + 1), (historyPMF bound index).toReal •
      ⟪left (fieldSample read runtime bound index), right (fieldSample read runtime bound index)⟫_ℂ := by
  rw [L2.inner_def]
  exact integral_source_sum read runtime bound _ (L2.integrable_inner (𝕜 := ℂ) left right).aestronglyMeasurable

end
end SourceConditionalTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
