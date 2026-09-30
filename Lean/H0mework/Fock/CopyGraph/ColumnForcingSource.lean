import H0mework.Fock.CopyGraph.DecoderSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceColumnForcing

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def column (depth : Nat) (index : Index depth) (actor : Nat) : SourceJointClockGraph.Carrier :=
  SourceCopyGraph.action depth index (SourceJointClockGraph.read (Finsupp.single actor (1 : ℂ)))

def samples (depth bound : Nat) (index : Index depth) (target : SourceJointClockGraph.Carrier)
    (actor : Fin (bound + 1)) : ℂ :=
  inner ℂ (column depth index actor.val) target / (Real.sqrt (historyPMF bound actor).toReal : ℂ)

def forcing (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) : Space (observed (historyPMF bound) query) :=
  transfer (historyPMF bound) query (taskValue (historyPMF bound) (samples depth bound index target))

omit [MeasurableSingletonClass Observed] in
theorem action_sum (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) :
    SourceConditionalGraphDecoder.action depth bound index query value =
      ∑ actor : Fin (bound + 1), ((Real.sqrt (historyPMF bound actor).toReal : ℂ) * value (query actor)) •
        column depth index actor.val := by
  change SourceCopyGraph.action depth index
    (SourceJointFiniteDecoder.read bound (pullback (historyPMF bound) query value)) = _
  rw [SourceJointFiniteDecoder.read, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro actor _
  change SourceCopyGraph.action depth index
    (((Real.sqrt (historyPMF bound actor).toReal : ℂ) * (pullback (historyPMF bound) query value) actor) •
      SourceJointClockGraph.read (Finsupp.single actor.val (1 : ℂ))) = _
  rw [map_smul, pullback_at _ _ _ _ (SourceUniformFibreVariance.source_positive bound actor)]
  rfl

omit [MeasurableSingletonClass Observed] in
theorem forcing_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    forcing depth bound index query target = (SourceConditionalGraphDecoder.action depth bound index query).adjoint target := by
  apply ext_inner_left ℂ
  intro value
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ value ((pullback (historyPMF bound) query).toContinuousLinearMap.adjoint
    (taskValue (historyPMF bound) (samples depth bound index target))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_source_sum, action_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro actor _
  change (historyPMF bound actor).toReal • inner ℂ ((pullback (historyPMF bound) query value) actor)
    ((taskValue (historyPMF bound) (samples depth bound index target)) actor) = _
  rw [pullback_at _ _ _ _ (SourceUniformFibreVariance.source_positive bound actor),
    taskValue_at _ _ _ (SourceUniformFibreVariance.source_positive bound actor), inner_smul_left]
  simp only [samples, RCLike.inner_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
  have positive := SourceGeneratedAtomicObservation.mass_positive (historyPMF bound) actor
    (SourceUniformFibreVariance.source_positive bound actor)
  have nonzero : (Real.sqrt (historyPMF bound actor).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr positive))
  have square : (Real.sqrt (historyPMF bound actor).toReal : ℂ) ^ 2 = ((historyPMF bound actor).toReal : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt positive)
  rw [← square]
  field_simp

theorem forcing_conditional (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) (atom : Observed)
    (supported : atom ∈ (observed (historyPMF bound) query).support) :
    forcing depth bound index query target atom =
      conditionalMean (historyPMF bound) query (samples depth bound index target) atom supported :=
  optimal_is_conditional (historyPMF bound) query (samples depth bound index target) atom supported

end
end SourceColumnForcing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
