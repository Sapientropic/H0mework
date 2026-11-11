import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixReadback

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def compatibleData (source : ι → H) (data : Coordinates ι) : Coordinates ι :=
  (Kernel (Projection.gram source))ᗮ.starProjection data

private theorem compatible_data (source : ι → H) (data : Coordinates ι) :
    Compatible (Projection.gram source) (compatibleData source data) := by
  intro w zero
  have within : compatibleData source data ∈ (Kernel (Projection.gram source))ᗮ :=
    Submodule.starProjection_apply_mem _ data
  exact (Submodule.mem_orthogonal _ _).mp within w zero

/-- Read the finite data in the actual Gram image and synthesize its unique source effect. -/
def inverse (source : ι → H) (data : Coordinates ι) : H :=
  sourceEffect (Projection.gram source) (Matrix.isHermitian_gram ℂ source)
    (compatibleData source data) (compatible_data source data)
    (Projection.synthesis source) (Projection.kernel_synthesis source)

/-- Any incompatible component of the input stays in the original finite Gram kernel. -/
theorem inverse_equation (source : ι → H) (data : Coordinates ι) :
    Projection.rhs source (inverse source data) = (Kernel (Projection.gram source))ᗮ.starProjection data := by
  let g := Projection.gram source
  let b := compatibleData source data
  let a := coefficients g (Matrix.isHermitian_gram ℂ source) b (compatible_data source data)
  have generated : inverse source data = Projection.synthesis source a := source_effect_eq _ _ _ _ _ _
  have solved : action g a = b := equation _ _ _ _
  ext i
  change inner ℂ (source i) (inverse source data) = b i
  rw [generated, ← Projection.action_read, solved]

theorem inverse_actual_rhs (source : ι → H) (x : H) :
    inverse source (Projection.rhs source x) = (Projection.sourceSpan source).starProjection x := by
  have compatible : Projection.rhs source x ∈ (Kernel (Projection.gram source))ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr (Projection.compatible source x)
  have same : compatibleData source (Projection.rhs source x) = Projection.rhs source x :=
    Submodule.starProjection_eq_self_iff.mpr compatible
  rw [← Projection.predictable_readback, Projection.predictable_source]
  exact (source_effect_of_equation _ _ _ _ _ _ _ ((Projection.equation source x).trans same.symm)).symm

omit [DecidableEq ι] in
private theorem source_span (source : ι → H) :
    Projection.sourceSpan source = Submodule.span ℂ (Set.range source) := by
  classical
  apply le_antisymm
  · rintro _ ⟨weights, rfl⟩
    change ∑ i, weights i • source i ∈ _
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let unit : Coordinates ι := PiLp.single 2 i (1 : ℂ)
    refine ⟨unit, ?_⟩
    change ∑ j, unit j • source j = source i
    rw [Finset.sum_eq_single i]
    · simp [unit]
    · intro j _ different
      simp only [unit, PiLp.single_apply, if_neg different, zero_smul]
    · exact fun absent => (absent (Finset.mem_univ _)).elim

variable [CompleteSpace H]

/-- Separating source tests give norm convergence of the finite Gram effects. -/
theorem inverse_tendsto (source : Nat → H)
    (separates : ∀ x : H, (∀ i : Nat, inner ℂ (source i) x = 0) → x = 0) (x : H) :
    Tendsto (fun n : Nat => inverse (fun i : Fin n => source i)
      (Projection.rhs (fun i : Fin n => source i) x)) atTop (𝓝 x) := by
  let span (n : Nat) := Projection.sourceSpan (fun i : Fin n => source i)
  have grows : Monotone span := by
    intro i j le
    change Projection.sourceSpan (fun k : Fin i => source k) ≤ Projection.sourceSpan (fun k : Fin j => source k)
    rw [source_span, source_span]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨Fin.castLE le k, rfl⟩
  have dense : (⨆ n, span n).topologicalClosure = ⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    refine le_antisymm ?_ bot_le
    intro y orthogonal
    rw [Submodule.mem_bot]
    apply separates y
    intro i
    have member : source i ∈ span (i+1) := by
      dsimp only [span]
      rw [source_span]
      exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩
    exact (Submodule.mem_orthogonal _ _).mp orthogonal _ (le_iSup span (i+1) member)
  simpa only [inverse_actual_rhs] using Submodule.starProjection_tendsto_self span grows x (le_of_eq dense.symm)

end SourceGeneratedFiniteGram.PrefixReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
