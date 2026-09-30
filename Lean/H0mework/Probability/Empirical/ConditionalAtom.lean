import H0mework.Probability.Empirical.ConditionalSamples

/-! An existing singleton L² cotest reads the original transfer as the full weighted next fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory
open scoped InnerProductSpace Classical

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

theorem nextAtom_eq_next_sample (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    nextAtom read runtime bound index = fieldSample read runtime.tick.next bound index := by
  rw [nextAtom, fieldSample, fieldPoint_action, ← nextSample_eq_successor, nextSample_eq_shift]
  rfl

def atomTest (runtime : LivingRuntimeState process) (bound : Nat) (atom : Field read) :
    Space read runtime.tick.next bound :=
  indicatorConstLp 2 (measurableSet_singleton atom) (measure_ne_top _ _) (1 : ℂ)

theorem atomTest_at_sample (runtime : LivingRuntimeState process) (bound : Nat) (atom : Field read)
    (index : Fin (bound + 1)) :
    atomTest read runtime bound atom (nextAtom read runtime bound index) =
      if nextAtom read runtime bound index = atom then 1 else 0 := by
  have raw := @indicatorConstLp_coeFn (Field read) _ _ 2 (empirical read runtime.tick.next bound).toMeasure _
    {atom} (measurableSet_singleton atom) (measure_ne_top _ _) (1 : ℂ)
  have sampled := ae_at_sample read runtime.tick.next bound index raw
  rw [← nextAtom_eq_next_sample] at sampled
  simpa only [atomTest, Set.indicator_apply, Set.mem_singleton_iff] using sampled

theorem transfer_atom_weighted (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Space read runtime bound) (atom : Field read) :
    (fieldPMF read runtime.tick.next bound atom).toReal • transfer read runtime bound value atom =
      ∑ index : Fin (bound + 1), (historyPMF bound index).toReal •
        (if nextAtom read runtime bound index = atom then value (fieldSample read runtime bound index) else 0) := by
  calc
    _ = ⟪atomTest read runtime bound atom, transfer read runtime bound value⟫_ℂ := by
      rw [atomTest, L2.inner_indicatorConstLp_one, integral_singleton]
      change _ = ((fieldPMF read runtime.tick.next bound).toMeasure {atom}).toReal • _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    _ = ⟪pullback read runtime bound (atomTest read runtime bound atom), value⟫_ℂ :=
      transfer_cotest read runtime bound _ value
    _ = _ := by
      rw [inner_source_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [pullback_at_sample, atomTest_at_sample]
      by_cases same : nextAtom read runtime bound index = atom <;> simp [same]

end
end SourceConditionalTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
