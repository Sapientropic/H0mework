import H0mework.Physics.LowEnergy.Quantum.WeakCoreEvolution
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Algebra.Module.TransferInstance

/-! Keep the common source family before taking a weak observer readout. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceFamilyHilbert
open Filter
open scoped Topology InnerProductSpace
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def boundedFamilies : Submodule ℂ (I → E) where
  carrier := {f | ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖f i‖ ≤ C}
  zero_mem' := ⟨0, le_rfl, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨C, hC, hf⟩ ⟨D, hD, hg⟩
    exact ⟨C+D, add_nonneg hC hD, fun i => (norm_add_le _ _).trans (add_le_add (hf i) (hg i))⟩
  smul_mem' := by
    rintro c f ⟨C, hC, hf⟩
    refine ⟨‖c‖*C, mul_nonneg (norm_nonneg c) hC, fun i => ?_⟩
    exact (norm_smul c (f i)).le.trans (mul_le_mul_of_nonneg_left (hf i) (norm_nonneg c))

@[ext] structure Family (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) where
  val : I → E
  property : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖val i‖ ≤ C

def familyEquiv (u : Ultrafilter I) : Family E u ≃ boundedFamilies (I := I) (E := E) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (u : Ultrafilter I) : AddCommGroup (Family E u) :=
  (familyEquiv u).addCommGroup
instance (u : Ultrafilter I) : Module ℂ (Family E u) :=
  (familyEquiv u).module ℂ

def value {u : Ultrafilter I} (f : Family E u) : I → E := f.val

def pair (u : Ultrafilter I) (f g : Family E u) : ℂ :=
  limUnder u (fun i => inner ℂ (value f i) (value g i))

theorem pair_tendsto (u : Ultrafilter I) (f g : Family E u) :
    Tendsto (fun i => inner ℂ (value f i) (value g i)) u (𝓝 (pair u f g)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨C, hC, hf⟩ := f.property
  obtain ⟨D, _, hg⟩ := g.property
  let p := fun i => inner ℂ (value f i) (value g i)
  have hb : Metric.closedBall (0 : ℂ) (C*D) ∈ u.map p := by
    change ∀ᶠ i in (u : Filter I), p i ∈ Metric.closedBall (0 : ℂ) (C*D)
    apply Filter.Eventually.of_forall
    intro i
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul (hf i) (hg i) (norm_nonneg _) hC)
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) (C*D)).ultrafilter_le_nhds' (u.map p) hb
  exact ⟨z, hz⟩

@[instance_reducible]
def preInner (u : Ultrafilter I) : PreInnerProductSpace.Core ℂ (Family E u) where
  inner := pair u
  conj_inner_symm f g := by
    apply tendsto_nhds_unique _ (pair_tendsto u f g)
    have h := (pair_tendsto u g f).star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (value g i) (value f i))) _
      (𝓝 ((starRingEnd ℂ) (pair u g f))) at h
    simpa only [inner_conj_symm] using h
  re_inner_nonneg f := by
    apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (pair_tendsto u f f))
    exact Filter.Eventually.of_forall (fun i => inner_self_nonneg (𝕜 := ℂ) (x := value f i))
  add_left f g h := by
    apply tendsto_nhds_unique (pair_tendsto u (f+g) h)
    change Tendsto (fun i => inner ℂ (value f i + value g i) (value h i)) _ _
    simpa only [inner_add_left] using
      (pair_tendsto u f h).add (pair_tendsto u g h)
  smul_left f g c := by
    apply tendsto_nhds_unique (pair_tendsto u (c • f) g)
    change Tendsto (fun i => inner ℂ (c • value f i) (value g i)) _ _
    simpa only [inner_smul_left] using
      tendsto_const_nhds.mul (pair_tendsto u f g)

instance (u : Ultrafilter I) : SeminormedAddCommGroup (Family E u) :=
  letI := preInner (E := E) u
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance (u : Ultrafilter I) : InnerProductSpace ℂ (Family E u) :=
  InnerProductSpace.ofCore (preInner (E := E) u)

abbrev Hilbert (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) := UniformSpace.Completion (Family E u)

def constant (u : Ultrafilter I) : E →ₗ[ℂ] Family E u where
  toFun x := ⟨fun _ => x, ‖x‖, norm_nonneg x, fun _ => le_rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constant_pair (u : Ultrafilter I) (x y : E) :
    inner ℂ (constant u x) (constant u y) = inner ℂ x y := by
  apply tendsto_nhds_unique (pair_tendsto u (constant u x) (constant u y))
  exact tendsto_const_nhds

def embed (u : Ultrafilter I) : E →ₗᵢ[ℂ] Hilbert E u :=
  UniformSpace.Completion.toComplₗᵢ.comp
    (LinearMap.isometryOfInner (constant u) (constant_pair u))

theorem inner_coe (u : Ultrafilter I) (f g : Family E u) :
    inner ℂ (f : Hilbert E u) (g : Hilbert E u) = pair u f g :=
  UniformSpace.Completion.inner_coe f g

theorem square_tendsto (u : Ultrafilter I) (f : Family E u) :
    Tendsto (fun i => ‖value f i‖^2) u (𝓝 (‖f‖^2)) := by
  have h := Complex.continuous_re.tendsto _ |>.comp (pair_tendsto u f f)
  change Tendsto (fun i => RCLike.re (inner ℂ (value f i) (value f i))) _
    (𝓝 (RCLike.re (inner ℂ f f))) at h
  simpa only [inner_self_eq_norm_sq] using h

theorem norm_tendsto (u : Ultrafilter I) (f : Family E u) :
    Tendsto (fun i => ‖value f i‖) u (𝓝 ‖f‖) := by
  have h := (Real.continuous_sqrt.tendsto _).comp (square_tendsto u f)
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h

theorem norm_le_of_eventually (u : Ultrafilter I) (f : Family E u) (C : ℝ)
    (h : ∀ᶠ i in (u : Filter I), ‖value f i‖ ≤ C) : ‖f‖ ≤ C :=
  le_of_tendsto (norm_tendsto u f) h

end LowEnergy.SourceFamilyHilbert
