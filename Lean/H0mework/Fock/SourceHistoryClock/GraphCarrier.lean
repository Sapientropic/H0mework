import H0mework.Fock.PrimeFieldJoint.ClockConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointClockGraph

open SourceSuccessorBoundary SourceClockComplex Filter
open scoped Topology
noncomputable section

abbrev Carrier := WithLp 2 (SourceMassCompletion.Joint × ℂ)

def read : (Nat →₀ ℂ) →ₗ[ℂ] Carrier :=
  (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).symm.toLinearMap.comp
    (SourceMassCompletion.jointRead.prod SourceClockComplex.clock)

def joint : Carrier →L[ℂ] SourceMassCompletion.Joint := WithLp.fstL 2 ℂ SourceMassCompletion.Joint ℂ

def clock : Carrier →L[ℂ] ℂ := WithLp.sndL 2 ℂ SourceMassCompletion.Joint ℂ

theorem read_apply (word : Nat →₀ ℂ) :
    read word = WithLp.toLp 2 (SourceMassCompletion.jointRead word, SourceClockComplex.clock word) := rfl

theorem joint_source (word : Nat →₀ ℂ) : joint (read word) = SourceMassCompletion.jointRead word := rfl

theorem clock_source (word : Nat →₀ ℂ) : clock (read word) = SourceClockComplex.clock word := rfl

theorem clock_unit_mem_closure : WithLp.toLp 2 ((0 : SourceMassCompletion.Joint), (1 : ℂ)) ∈
    read.range.topologicalClosure := by
  have pair := SourceClockComplex.scaled_joint_tendsto.prodMk_nhds (tendsto_const_nhds (x := (1 : ℂ)))
  have lifted := (WithLp.prod_continuous_toLp 2 SourceMassCompletion.Joint ℂ).continuousAt.tendsto.comp pair
  have generated : Tendsto (fun bound => read (densityScale bound • meanWord bound)) atTop
      (𝓝 (WithLp.toLp 2 ((0 : SourceMassCompletion.Joint), (1 : ℂ)))) := by
    simpa only [Function.comp_def, read_apply, density_clock] using lifted
  exact mem_closure_of_tendsto generated (Eventually.of_forall fun bound => ⟨_, rfl⟩)

theorem clock_axis_mem_closure (scalar : ℂ) :
    WithLp.toLp 2 ((0 : SourceMassCompletion.Joint), scalar) ∈ read.range.topologicalClosure := by
  have scaled := read.range.topologicalClosure.smul_mem scalar clock_unit_mem_closure
  simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using scaled

private theorem joint_source_mem_closure (word : Nat →₀ ℂ) :
    WithLp.toLp 2 (SourceMassCompletion.jointRead word, (0 : ℂ)) ∈ read.range.topologicalClosure := by
  have source := read.range.le_topologicalClosure (show read word ∈ read.range from ⟨word, rfl⟩)
  have subtract := read.range.topologicalClosure.sub_mem source
    (clock_axis_mem_closure (SourceClockComplex.clock word))
  simpa only [read_apply, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero, sub_self] using subtract

theorem joint_axis_mem_closure (value : SourceMassCompletion.Joint) :
    WithLp.toLp 2 (value, (0 : ℂ)) ∈ read.range.topologicalClosure := by
  let inclusion : SourceMassCompletion.Joint →L[ℂ] Carrier :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ SourceMassCompletion.Joint ℂ)
  have sourceIncluded : SourceMassCompletion.jointRead.range ≤
      read.range.topologicalClosure.comap inclusion.toLinearMap := by
    rintro _ ⟨word, rfl⟩
    exact joint_source_mem_closure word
  have whole := Submodule.topologicalClosure_minimal SourceMassCompletion.jointRead.range sourceIncluded
    (read.range.isClosed_topologicalClosure.preimage inclusion.continuous)
  rw [SourceMassCompletion.range_jointRead_closure_eq_top] at whole
  exact whole (show value ∈ (⊤ : Submodule ℂ SourceMassCompletion.Joint) from trivial)

theorem range_read_closure_eq_top : read.range.topologicalClosure = ⊤ := by
  apply top_unique
  intro value _
  have combined := read.range.topologicalClosure.add_mem
    (joint_axis_mem_closure (joint value)) (clock_axis_mem_closure (clock value))
  simp only [joint, clock, WithLp.fstL_apply, WithLp.sndL_apply, ← WithLp.toLp_add,
    Prod.mk_add_mk, add_zero, zero_add] at combined
  change WithLp.toLp 2 (WithLp.ofLp value) ∈ _ at combined
  simpa only [WithLp.toLp_ofLp] using combined

theorem read_denseRange : DenseRange read :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr range_read_closure_eq_top

theorem native_read (word : Nat →₀ ℤ) :
    read (ofNative word) = WithLp.toLp 2 (SourceMassCompletion.nativeRead word,
      (SourceClockModel.clockRead (SourceClockModel.projection word) : ℂ)) := by
  rw [read_apply, joint_native, model_source]

end
end SourceJointClockGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
