import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussUnitaryCore

/-! The original full label resolution acts before exponentiation and weak observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussGradedCompression
open GaussCoreHilbert GaussDiagonalHistory NativeHistoryGrade GaussUnitaryHistory
open SymmetricGraphClosure Filter
open scoped InnerProductSpace Topology
local instance labelFintype : Fintype Label := Fintype.ofFinite _

def piece (g : Label) (x : diagonal.domain) : diagonal.domain :=
  ⟨projection g (x : H), GaussDiagonalGrade.stable g x⟩

theorem piece_action (g : Label) (x : diagonal.domain) :
    diagonal (piece g x) = projection g (diagonal x) := GaussDiagonalGrade.diagonal_commutes g x

def compression (F : Index) : H →L[ℂ] H :=
  ∑ g : Label, projection g * FiniteCoreEvolution.compression diagonal F * projection g

theorem compression_apply (F : Index) (x : H) :
    compression F x = ∑ g : Label, projection g (FiniteCoreEvolution.compression diagonal F (projection g x)) := by
  simp only [compression, sum_apply, mul_apply_eq_comp]

theorem compression_pair (F : Index) : (compression F).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, compression_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact (projection_symmetric g _ _).trans
    ((FiniteCoreEvolution.compression_symmetric diagonal diagonal_pair F _ _).trans
      (projection_symmetric g _ _))

theorem compression_selfAdjoint (F : Index) : IsSelfAdjoint (compression F) :=
  (compression_pair F).isSelfAdjoint

theorem left_block (F : Index) (g : Label) : projection g * compression F =
    projection g * FiniteCoreEvolution.compression diagonal F * projection g := by
  calc
    _ = ∑ h : Label, (projection g * projection h) *
        FiniteCoreEvolution.compression diagonal F * projection h := by
      simp only [compression, Finset.mul_sum, mul_assoc]
    _ = _ := by simp [projection_product, ite_mul]

theorem right_block (F : Index) (g : Label) : compression F * projection g =
    projection g * FiniteCoreEvolution.compression diagonal F * projection g := by
  calc
    _ = ∑ h : Label, projection h * FiniteCoreEvolution.compression diagonal F *
        (projection h * projection g) := by
      simp only [compression, Finset.sum_mul, mul_assoc]
    _ = _ := by simp [projection_product, mul_ite]

theorem compression_commutes (F : Index) (g : Label) : Commute (projection g) (compression F) := by
  show projection g * compression F = compression F * projection g
  rw [left_block, right_block]

theorem projection_idempotent (g : Label) (x : H) : projection g (projection g x) = projection g x := by
  have h := congrArg (fun A : H →L[ℂ] H => A x) (projection_product g g)
  simpa only [if_true, mul_apply_eq_comp, Function.comp_apply] using h

theorem compression_core_exact (F : Index) (x : diagonal.domain)
    (contains : ∀ g : Label, piece g x ∈ F)
    (contains_next : ∀ g : Label, piece g ⟨diagonal x, diagonal_invariant x⟩ ∈ F) :
    compression F (x : H) = diagonal x := by
  have he (g : Label) : FiniteCoreEvolution.compression diagonal F (projection g (x : H)) =
      projection g (diagonal x) := by
    have he := FiniteCoreEvolution.compression_core_exact diagonal F (piece g x)
      (diagonal_invariant (piece g x)) (contains g)
    have hi : (⟨diagonal (piece g x), diagonal_invariant (piece g x)⟩ : diagonal.domain) =
        piece g ⟨diagonal x, diagonal_invariant x⟩ := Subtype.ext (piece_action g x)
    rw [hi] at he
    exact (he (contains_next g)).trans (piece_action g x)
  rw [compression_apply]
  simp_rw [he, projection_idempotent]
  rw [← sum_apply, projection_resolution, one_apply_eq_self]

theorem compression_core_bound (F : Index) (x : diagonal.domain)
    (contains : ∀ g : Label, piece g x ∈ F) : ‖compression F (x : H)‖ ≤ ‖diagonal x‖ := by
  have hb (g : Label) :
      ‖projection g (FiniteCoreEvolution.compression diagonal F (projection g (x : H)))‖ ≤
        ‖projection g (diagonal x)‖ := by
    have hc := FiniteCoreEvolution.compression_core_bound diagonal F (piece g x)
      (FiniteCoreEvolution.mem_coreSpan diagonal F (piece g x) (contains g))
    have hp := piece_bound g (FiniteCoreEvolution.compression diagonal F (projection g (x : H)))
    exact (hp.trans hc).trans_eq (congrArg norm (piece_action g x))
  have hs : ‖compression F (x : H)‖^2 ≤ ‖diagonal x‖^2 := by
    rw [compression_apply, norm_sum_projection, ← norm_resolution (diagonal x)]
    exact Finset.sum_le_sum (fun g _ => pow_le_pow_left₀ (norm_nonneg _) (hb g) 2)
  nlinarith [norm_nonneg (compression F (x : H)), norm_nonneg (diagonal x)]

def support (x : diagonal.domain) : Index := by
  classical
  exact Finset.univ.image (fun g : Label => piece g x)

theorem eventually_contains (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ g : Label, piece g x ∈ F := by
  classical
  apply WeakCoreEvolution.sourceFilter_cofinal diagonal
  refine Filter.eventually_atTop.mpr ⟨support x, fun F hF g => hF ?_⟩
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩

theorem eventually_exact (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), compression F (x : H) = diagonal x := by
  filter_upwards [eventually_contains x,
    eventually_contains ⟨diagonal x, diagonal_invariant x⟩] with F h hnext
  exact compression_core_exact F x h hnext

#print axioms compression_selfAdjoint
#print axioms compression_commutes
#print axioms compression_core_bound
#print axioms eventually_exact
end LowEnergy.GaussGradedCompression
