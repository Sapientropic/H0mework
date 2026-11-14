import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.LinearReadback

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixImage.ContactFibre

open scoped InnerProductSpace Topology
open Filter
open private source_span from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*}
variable (S : Submodule ℂ H) [CompleteSpace S]

/-- Observations use their restrictions to the actual closed source domain. -/
def restrictTests (test : ι → H) (i : ι) : S := S.orthogonalProjectionOnto (test i)

theorem restricted_read (test : ι → H) (x : S) :
    Projection.rhs (restrictTests S test) x = Projection.rhs test (x : H) := by
  ext i
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right x (test i)

variable [Fintype ι] [DecidableEq ι]

def recover (test : ι → H) : Coordinates ι →ₗ[ℂ] S :=
  PrefixReadback.inverseLinear (restrictTests S test)

theorem recover_equation (test : ι → H) (data : Coordinates ι) (x : S)
    (observed : data = Projection.rhs test (x : H)) :
    Projection.rhs test (recover S test data : H) = data := by
  let pulled := restrictTests S test
  have same : data = Projection.rhs pulled x :=
    observed.trans (restricted_read S test x).symm
  have image : data ∈ (Kernel (Projection.gram pulled))ᗮ := by
    rw [same]
    exact (Submodule.mem_orthogonal _ _).mpr (Projection.compatible pulled x)
  have solved := PrefixReadback.inverse_equation pulled data
  rw [Submodule.starProjection_eq_self_iff.mpr image] at solved
  have lifted : recover S test data = PrefixReadback.inverse pulled data :=
    PrefixReadback.inverseLinear_apply pulled data
  exact (restricted_read S test (recover S test data)).symm.trans
    ((congrArg (Projection.rhs pulled) lifted).trans solved)

theorem recover_projection (test : ι → H) (x : S) :
    recover S test (Projection.rhs test (x : H)) =
      (Projection.sourceSpan (restrictTests S test)).starProjection x := by
  let pulled := restrictTests S test
  rw [← restricted_read S test x, recover, PrefixReadback.inverseLinear_apply]
  exact PrefixReadback.inverse_actual_rhs pulled x

/-- The new fit obeys the original observations, and its residual is orthogonal to every observation in the domain. -/
theorem recover_energy (test : ι → H) (x : S) :
    let fit := recover S test (Projection.rhs test (x : H))
    ‖x‖^2 = ‖fit‖^2 + ‖x-fit‖^2 ∧
      (∀ i, inner ℂ (test i) ((x-fit : S) : H) = 0) := by
  let fit := recover S test (Projection.rhs test (x : H))
  let pulled := restrictTests S test
  have projection : fit = (Projection.sourceSpan pulled).starProjection x :=
    recover_projection S test x
  refine ⟨?_, ?_⟩
  · have source := Submodule.norm_sq_eq_add_norm_sq_starProjection x (Projection.sourceSpan pulled)
    rw [Submodule.starProjection_orthogonal_val, ← projection] at source
    exact source
  · intro i
    have exactPrice := congrArg (fun d : Coordinates ι => d i)
      (recover_equation S test (Projection.rhs test (x : H)) x rfl)
    change inner ℂ (test i) (fit : H) = inner ℂ (test i) (x : H) at exactPrice
    rw [Submodule.coe_sub, inner_sub_right, exactPrice, sub_self]

/-- A larger observation bank can only decrease the true reconstruction error. -/
theorem recover_error_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (small : ι → H) (large : κ → H) (embedding : ι → κ)
    (same : ∀ i, large (embedding i) = small i) (x : S) :
    ‖x-recover S large (Projection.rhs large (x : H))‖ ≤
      ‖x-recover S small (Projection.rhs small (x : H))‖ := by
  let U := Projection.sourceSpan (restrictTests S small)
  let V := Projection.sourceSpan (restrictTests S large)
  have subset : U ≤ V := by
    change Projection.sourceSpan (restrictTests S small) ≤ Projection.sourceSpan (restrictTests S large)
    rw [source_span, source_span]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨embedding i, congrArg S.orthogonalProjectionOnto (same i)⟩
  rw [recover_projection, recover_projection]
  change ‖x-V.starProjection x‖ ≤ ‖x-U.starProjection x‖
  rw [Submodule.starProjection_minimal]
  let candidate : V := ⟨U.starProjection x, subset (Submodule.starProjection_apply_mem U x)⟩
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ candidate

/-- Restriction of separating tests is still separating on the source domain. -/
theorem restricted_separates (test : Nat → H)
    (separates : ∀ x : H, (∀ i, inner ℂ (test i) x = 0) → x = 0) :
    ∀ x : S, (∀ i, inner ℂ (S.orthogonalProjectionOnto (test i)) x = 0) → x = 0 := by
  intro x silent
  apply Subtype.ext
  apply separates
  intro i
  exact (S.inner_orthogonalProjectionOnto_eq_of_mem_right x (test i)).symm.trans (silent i)

/-- Prefixes of the same original tests recover the complete constrained source. -/
theorem recover_tendsto (test : Nat → H)
    (separates : ∀ x : H, (∀ i, inner ℂ (test i) x = 0) → x = 0) (x : S) :
    Tendsto (fun n => recover S (fun i : Fin n => test i.val)
      (Projection.rhs (fun i : Fin n => test i.val) (x : H))) atTop (𝓝 x) := by
  have paid := PrefixReadback.inverse_tendsto (fun i : Nat => S.orthogonalProjectionOnto (test i))
    (restricted_separates S test separates) x
  refine paid.congr' (Eventually.of_forall fun n => ?_)
  let family : Fin n → H := fun i => test i.val
  change PrefixReadback.inverse (restrictTests S family) (Projection.rhs (restrictTests S family) x) =
    recover S family (Projection.rhs family (x : H))
  rw [recover, PrefixReadback.inverseLinear_apply, restricted_read]

/-- Refinements retaining every separating prefix recover the same constrained source. -/
theorem recover_refined_tendsto {κ : Nat → Type*} [∀ n, Fintype (κ n)]
    [∀ n, DecidableEq (κ n)] (test : Nat → H)
    (separates : ∀ x : H, (∀ i, inner ℂ (test i) x = 0) → x = 0)
    (large : (n : Nat) → κ n → H) (embed : (n : Nat) → Fin n → κ n)
    (same : ∀ (n : Nat) (i : Fin n), large n (embed n i) = test i.val)
    (data : (n : Nat) → Coordinates (κ n)) (x : S)
    (observed : ∀ n, data n = Projection.rhs (large n) (x : H)) :
    Tendsto (fun n => recover S (large n) (data n)) atTop (𝓝 x) := by
  let small (n : Nat) : Fin n → H := fun i => test i.val
  let smallFit (n : Nat) : S := recover S (small n) (Projection.rhs (small n) (x : H))
  have converges : Tendsto smallFit atTop (𝓝 x) := recover_tendsto S test separates x
  have negligible := ((tendsto_const_nhds (x := x)).sub converges).norm
  rw [sub_self, norm_zero] at negligible
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) negligible
  rw [norm_sub_rev, observed n]
  exact recover_error_le S (small n) (large n) (embed n) (same n) x

end SourceGeneratedFiniteGram.PrefixImage.ContactFibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
