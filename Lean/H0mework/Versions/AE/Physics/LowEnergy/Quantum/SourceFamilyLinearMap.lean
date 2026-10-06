import H0mework.Physics.LowEnergy.Quantum.SourceFamilyOperator

/-! Actual finite-family time integrals return to the unchanged source Hilbert carrier. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FullYSourceFamilyLinearMap
open SourceFamilyHilbert Filter
open scoped Topology InnerProductSpace
variable {I E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def act (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) : Family E u →ₗ[ℂ] Family F u where
  toFun f := ⟨fun i => A i (value f i), by
    obtain ⟨D,hD,hf⟩ := f.property
    refine ⟨C*D,mul_nonneg hC hD,fun i => ?_⟩
    exact (hA i _).trans (mul_le_mul_of_nonneg_left (hf i) hC)⟩
  map_add' f g := by
    apply Family.ext
    funext i
    exact map_add (A i) (value f i) (value g i)
  map_smul' c f := by
    apply Family.ext
    funext i
    exact map_smul (A i) c (value f i)

theorem act_bound (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) (f : Family E u) :
    ‖act u A C hC hA f‖ ≤ C*‖f‖ :=
  le_of_tendsto_of_tendsto (norm_tendsto u (act u A C hC hA f))
    ((norm_tendsto u f).const_mul C) (Filter.Eventually.of_forall (fun i => hA i (value f i)))

def lift (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) : Hilbert E u →L[ℂ] Hilbert F u :=
  (UniformSpace.Completion.toComplL.comp
    ((act u A C hC hA).mkContinuous C (act_bound u A C hC hA))).extend
      UniformSpace.Completion.toComplL

theorem lift_coe (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) (f : Family E u) :
    lift u A C hC hA (f : Hilbert E u)=(act u A C hC hA f : Hilbert F u) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) f

theorem lift_bound (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) (x : Hilbert E u) :
    ‖lift u A C hC hA x‖ ≤ C*‖x‖ := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  exact act_bound u A C hC hA f

theorem lift_strong_limit (u : Ultrafilter I) (A : I → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i x, ‖A i x‖ ≤ C*‖x‖) (f : ℕ → Hilbert E u) (y : Hilbert E u)
    (h : Tendsto f atTop (𝓝 y)) :
    Tendsto (fun n => lift u A C hC hA (f n)) atTop (𝓝 (lift u A C hC hA y)) :=
  (lift u A C hC hA).continuous.tendsto y |>.comp h

#print axioms lift_coe
#print axioms lift_bound
end LowEnergy.FullYSourceFamilyLinearMap
