import H0mework.Fock.HistoryConditional.InventoryConditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability
open scoped Classical
noncomputable section

def bornObservation (bound depth : Nat) := observation (bound + 1) depth (Fin.last (bound + 1))

theorem born_supported (bound depth : Nat) :
    bornObservation bound depth ∈ ((historyPMF (bound + 1)).map (observation (bound + 1) depth)).support :=
  SourceWeightedRecovery.observed_supported _ _ (Fin.last (bound + 1))
    (by simp only [historyPMF, PMF.mem_support_uniformOfFintype])

theorem new_support_iff (bound depth : Nat) (value : SourceGeneratedScalarCofinalTopology.NativeProbability.Field SourceObservationInvariantControls.parity) :
    value ∈ ((historyPMF (bound + 1)).map (observation (bound + 1) depth)).support ↔
      value ∈ ((historyPMF bound).map (observation bound depth)).support ∨ value = bornObservation bound depth := by
  constructor
  · intro supported
    obtain ⟨i, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have origin (i : Fin (bound + 2)) : observation (bound + 1) depth i = value →
        value ∈ ((historyPMF bound).map (observation bound depth)).support ∨ value = bornObservation bound depth := by
      refine Fin.lastCases (fun equality => Or.inr equality.symm) (fun j equality => ?_) i
      exact Or.inl ((PMF.mem_support_map_iff _ _ _).mpr
        ⟨j, by simp only [historyPMF, PMF.mem_support_uniformOfFintype],
          (observation_retained bound depth j).symm.trans equality⟩)
    exact origin i same
  · rintro (old | rfl)
    · exact supported_retained bound depth value old
    · exact born_supported bound depth

theorem fresh_posterior (bound depth : Nat)
    (fresh : bornObservation bound depth ∉ ((historyPMF bound).map (observation bound depth)).support) :
    conditional (bound + 1) depth (bornObservation bound depth) (born_supported bound depth) = PMF.pure (Fin.last (bound + 1)) := by
  have absent (i : Fin (bound + 1)) : observation bound depth i ≠ bornObservation bound depth := by
    intro same
    exact fresh ((PMF.mem_support_map_iff _ _ _).mpr
      ⟨i, by simp only [historyPMF, PMF.mem_support_uniformOfFintype], same⟩)
  have unique (i : Fin (bound + 2)) : observation (bound + 1) depth i = bornObservation bound depth → i = Fin.last (bound + 1) := by
    refine Fin.lastCases (fun _ => rfl) (fun j same => ?_) i
    exact (absent j ((observation_retained bound depth j).symm.trans same)).elim
  have weight : (historyPMF (bound + 1)).map (observation (bound + 1) depth) (bornObservation bound depth) =
      historyPMF (bound + 1) (Fin.last (bound + 1)) := by
    rw [PMF.map_apply, tsum_eq_single (Fin.last (bound + 1))]
    · exact if_pos rfl
    · intro i different
      exact if_neg (fun same => different (unique i same.symm))

  apply PMF.ext
  intro i
  rw [conditional, SourceConditionalHistory.conditional_apply, weight, PMF.pure_apply]
  by_cases same : i = Fin.last (bound + 1)
  · subst i
    rw [bornObservation, if_pos rfl, if_pos rfl]
    have positive : Fin.last (bound + 1) ∈ (historyPMF (bound + 1)).support := by
      simp only [historyPMF, PMF.mem_support_uniformOfFintype]
    exact ENNReal.mul_inv_cancel positive ((historyPMF (bound + 1)).apply_ne_top _)
  · rw [if_neg (fun equality => same (unique i equality)), if_neg same]

theorem fresh_recovers (bound depth : Nat)
    (fresh : bornObservation bound depth ∉ ((historyPMF bound).map (observation bound depth)).support) :
    SourceVectorMoment.mean (conditional (bound + 1) depth (bornObservation bound depth) (born_supported bound depth)) (values (bound + 1)) = born bound := by
  rw [fresh_posterior bound depth fresh, SourceVectorMoment.mean, Finset.sum_eq_single (Fin.last (bound + 1))]
  · simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    rfl
  · intro i _ different
    rw [PMF.pure_apply, if_neg different]
    simp only [ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem fresh_variance_zero (bound depth : Nat)
    (fresh : bornObservation bound depth ∉ ((historyPMF bound).map (observation bound depth)).support) :
    SourceVectorMoment.variance (conditional (bound + 1) depth (bornObservation bound depth) (born_supported bound depth)) (values (bound + 1)) = 0 := by
  rw [SourceVectorMoment.variance, fresh_recovers bound depth fresh, fresh_posterior bound depth fresh]
  rw [SourceVectorMoment.error]
  apply Finset.sum_eq_zero
  intro i _
  by_cases same : i = Fin.last (bound + 1)
  · subst i
    simp only [born, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · rw [PMF.pure_apply, if_neg same]
    simp only [ENNReal.toReal_zero, zero_mul]

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
