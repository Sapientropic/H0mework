import H0mework.Versions.X.Fock.HistoryConditional.InformationLossEntropy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedRuntimeHistoryProbability (historyPMF)
open SourceUniformFibreVariance (fibre fibre_mem)
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem fine_mass (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse)
    (supported : value ∈ ((historyPMF bound).map (fun actor : Fin (bound + 1) => forget (read actor.val))).support)
    (actor : Fin (bound + 1)) (seen : forget (read actor.val) = value) :
    (SourceConditionalNext.conditionalNext (historyPMF bound) (fun index : Fin (bound + 1) => forget (read index.val))
      (SourceConditionalNext.Image.actual (fun index : Fin (bound + 1) => read index.val)) value supported
      (SourceConditionalNext.Image.actual (fun index : Fin (bound + 1) => read index.val) actor)).toReal =
      ((SourceConditionalNativeObservers.generate read bound (read actor.val)).1 : ℝ) /
        (SourceConditionalNativeMerge.count read forget bound (SourceConditionalNativeObservers.generate read bound) value : ℝ) := by
  classical
  have comparison (index : Fin (bound + 1)) :
      SourceConditionalNext.Image.actual (fun i : Fin (bound + 1) => read i.val) actor =
        SourceConditionalNext.Image.actual (fun i : Fin (bound + 1) => read i.val) index ↔ read index.val = read actor.val :=
    ⟨fun same => (congrArg Subtype.val same).symm, fun same => Subtype.ext same.symm⟩
  have raw : SourceConditionalNext.conditionalNext (historyPMF bound) (fun index : Fin (bound + 1) => forget (read index.val))
      (SourceConditionalNext.Image.actual (fun index : Fin (bound + 1) => read index.val)) value supported
      (SourceConditionalNext.Image.actual (fun index : Fin (bound + 1) => read index.val) actor) =
      ∑ index ∈ fibre bound (fun i => read i.val) (read actor.val),
        SourceConditionalHistory.conditional (historyPMF bound) (fun i : Fin (bound + 1) => forget (read i.val)) value supported index := by
    rw [SourceConditionalNext.conditionalNext, PMF.map_apply, tsum_fintype, fibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index _
    rw [comparison]
    split_ifs <;> rfl
  rw [raw, ENNReal.toReal_sum (fun index _ => PMF.apply_ne_top _ index)]
  have weights (index : Fin (bound + 1)) (inside : index ∈ fibre bound (fun i => read i.val) (read actor.val)) :
      (SourceConditionalHistory.conditional (historyPMF bound) (fun i : Fin (bound + 1) => forget (read i.val)) value supported index).toReal =
        ((fibre bound (fun i : Fin (bound + 1) => forget (read i.val)) value).card : ℝ)⁻¹ := by
    rw [SourceUniformFibreVariance.conditional_weight]
    apply if_pos
    apply (fibre_mem _ _ _ _).mpr
    exact (congrArg forget ((fibre_mem _ _ _ _).mp inside)).trans seen
  rw [Finset.sum_congr rfl weights, Finset.sum_const, nsmul_eq_mul,
    SourceConditionalNativeMerge.count_generated, SourceConditionalNativePosterior.count_fibre,
    SourceConditionalNativePosterior.count_fibre]
  rfl

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
