import H0mework.Probability.MassCompletion.Mean

/-! Finite source points and their generated mass limit cover the whole joint carrier after closure. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary Filter
open scoped Topology

noncomputable section

theorem basis_axis_mem_closure (index : Nat) (scalar : ℂ) :
    WithLp.toLp 2 (scalar • basis index, (0 : ℂ)) ∈ jointRead.range.topologicalClosure := by
  have source := jointRead.range.le_topologicalClosure
    (show jointRead (Finsupp.single index scalar) ∈ jointRead.range from ⟨_, rfl⟩)
  rw [jointRead_single] at source
  have difference := jointRead.range.topologicalClosure.sub_mem source (mass_axis_mem_closure scalar)
  simpa only [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero, sub_self] using difference

theorem first_axis_mem_closure (value : H) :
    WithLp.toLp 2 (value, (0 : ℂ)) ∈ jointRead.range.topologicalClosure := by
  let inclusion : H →L[ℂ] Joint :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ H ℂ)
  have sourceSum := inclusion.hasSum (lp.hasSum_single (p := 2) (by norm_num) value)
  change inclusion value ∈ jointRead.range.topologicalClosure
  apply jointRead.range.isClosed_topologicalClosure.mem_of_tendsto sourceSum
  apply Eventually.of_forall
  intro finite
  apply jointRead.range.topologicalClosure.sum_mem
  intro index _
  change WithLp.toLp 2 (lp.single (E := fun _ : Nat => ℂ) 2 index (value index), (0 : ℂ)) ∈ _
  simpa only [basis, ← lp.single_smul, smul_eq_mul, mul_one] using
    basis_axis_mem_closure index (value index)

theorem range_jointRead_closure_eq_top : jointRead.range.topologicalClosure = ⊤ := by
  apply top_unique
  intro value _
  have joined := jointRead.range.topologicalClosure.add_mem
    (first_axis_mem_closure (firstRead value)) (mass_axis_mem_closure (massRead value))
  simp only [← WithLp.toLp_add, Prod.mk_add_mk, zero_add, add_zero, firstRead, massRead,
    WithLp.fstL_apply, WithLp.sndL_apply] at joined
  change WithLp.toLp 2 (WithLp.ofLp value) ∈ _ at joined
  simpa only [WithLp.toLp_ofLp] using joined

theorem jointRead_denseRange : DenseRange jointRead :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr range_jointRead_closure_eq_top

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
