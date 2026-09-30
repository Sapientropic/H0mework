import H0mework.Probability.MassCompletion.Carrier
import H0mework.Probability.SourceShift.Mean

/-! The original normalized source words generate the independent mass direction in the joint closure. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary Filter
open scoped Topology

noncomputable section

theorem source_mean_tendsto :
    Tendsto (fun bound => jointRead (meanWord bound)) atTop
      (𝓝 (WithLp.toLp 2 ((0 : H), (1 : ℂ)))) := by
  have pair := mean_tendsto_zero.prodMk_nhds (tendsto_const_nhds (x := (1 : ℂ)))
  have joint := (WithLp.prod_continuous_toLp 2 H ℂ).continuousAt.tendsto.comp pair
  simpa only [Function.comp_def, jointRead_apply, mass_meanWord, mean] using joint

theorem mass_unit_mem_closure :
    WithLp.toLp 2 ((0 : H), (1 : ℂ)) ∈ jointRead.range.topologicalClosure :=
  mem_closure_of_tendsto source_mean_tendsto
    (Eventually.of_forall fun bound => ⟨meanWord bound, rfl⟩)

theorem mass_axis_mem_closure (scalar : ℂ) :
    WithLp.toLp 2 ((0 : H), scalar) ∈ jointRead.range.topologicalClosure := by
  have scaled := jointRead.range.topologicalClosure.smul_mem scalar mass_unit_mem_closure
  simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using scaled

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
