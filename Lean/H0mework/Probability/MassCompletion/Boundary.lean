import H0mework.Probability.MassCompletion.Action
import H0mework.Probability.SourceShift.Closure

/-! The joint source completion preserves exactly the original mass quotient of finite boundaries. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary Filter
open scoped Topology

noncomputable section

private abbrev boundaryRange : Submodule ℂ Joint :=
  (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range

private theorem unit_mem_boundary_closure :
    WithLp.toLp 2 (basis 0, (0 : ℂ)) ∈ boundaryRange.topologicalClosure := by
  have first : Tendsto (fun bound => basis 0 - mean bound) atTop (𝓝 (basis 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub mean_tendsto_zero
  have combined := (WithLp.prod_continuous_toLp 2 H ℂ).continuousAt.tendsto.comp
    (first.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ))))
  apply mem_closure_of_tendsto combined
  apply Eventually.of_forall
  intro bound
  refine ⟨-certificate ℂ (meanWord bound), ?_⟩
  change jointRead (SourceSuccessorBoundary.boundary ℂ (-certificate ℂ (meanWord bound))) = _
  rw [jointRead_apply, mass_boundary, readWord_boundary, map_neg, map_neg,
    difference_certificate_mean, neg_sub]
  rfl

private theorem basis_mem_boundary_closure (index : Nat) :
    WithLp.toLp 2 (basis index, (0 : ℂ)) ∈ boundaryRange.topologicalClosure := by
  have initialSegment : WithLp.toLp 2 (basis index - basis 0, (0 : ℂ)) ∈ boundaryRange := by
    refine ⟨∑ source ∈ Finset.range index, Finsupp.single source (1 : ℂ), ?_⟩
    change jointRead (SourceSuccessorBoundary.boundary ℂ _) = _
    simp only [boundary_prefix, map_sub, jointRead_single, one_smul,
      ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  have joined := boundaryRange.topologicalClosure.add_mem
    (boundaryRange.le_topologicalClosure initialSegment) unit_mem_boundary_closure
  simpa only [← WithLp.toLp_add, Prod.mk_add_mk, sub_add_cancel, zero_add] using joined

private theorem first_mem_boundary_closure (value : H) :
    WithLp.toLp 2 (value, (0 : ℂ)) ∈ boundaryRange.topologicalClosure := by
  let inclusion : H →L[ℂ] Joint :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ H ℂ)
  have sourceSum := inclusion.hasSum (lp.hasSum_single (p := 2) (by norm_num) value)
  change inclusion value ∈ boundaryRange.topologicalClosure
  apply boundaryRange.isClosed_topologicalClosure.mem_of_tendsto sourceSum
  apply Eventually.of_forall
  intro finite
  apply boundaryRange.topologicalClosure.sum_mem
  intro index _
  have scaled := boundaryRange.topologicalClosure.smul_mem (value index)
    (basis_mem_boundary_closure index)
  change WithLp.toLp 2 (lp.single (E := fun _ : Nat => ℂ) 2 index (value index), (0 : ℂ)) ∈ _
  simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero, basis, ← lp.single_smul,
    smul_eq_mul, mul_one, mul_zero] using scaled

theorem source_boundary_closure_eq_ker_massRead :
    (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range.topologicalClosure = massRead.ker := by
  apply le_antisymm
  · apply boundaryRange.topologicalClosure_minimal _ massRead.isClosed_ker
    rintro value ⟨word, rfl⟩
    exact mass_boundary ℂ word
  · intro value zeroMass
    have source := first_mem_boundary_closure (firstRead value)
    change massRead value = 0 at zeroMass
    rw [← zeroMass] at source
    change WithLp.toLp 2 (WithLp.ofLp value) ∈ _ at source
    simpa only [WithLp.toLp_ofLp] using source

theorem massRead_fibre_iff (left right : Joint) :
    massRead left = massRead right ↔
      left - right ∈ (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range.topologicalClosure := by
  rw [source_boundary_closure_eq_ker_massRead]
  change massRead left = massRead right ↔ massRead (left - right) = 0
  rw [map_sub, sub_eq_zero]

theorem mass_axis_not_mem_boundary_closure :
    WithLp.toLp 2 ((0 : H), (1 : ℂ)) ∉
      (jointRead.comp (SourceSuccessorBoundary.boundary ℂ)).range.topologicalClosure := by
  rw [source_boundary_closure_eq_ker_massRead]
  change (1 : ℂ) ≠ 0
  exact one_ne_zero

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
