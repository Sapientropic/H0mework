import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCutoff
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedLocalCurrent

/-! The original G=0 readout retains all Number sectors, including the
source-created N2 and removed N0 states. It changes no source preparation. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumConfigurationHilbert GaussCoreHilbert NativeHistoryGrade
open GaussYukawaGrade FullYSourceCutoffVolterra CanonicalGradedCurrent
open scoped InnerProductSpace BigOperators
local instance projectionLabelFintype : Fintype Label := Fintype.ofFinite _

def gradeZeroPiece (x : H) : H :=
  WithLp.toLp 2 (fun word => if (NativeHistoryGrade.sourceLabel word).2=0 then x word else 0)

theorem grade_zero_piece_bound (x : H) : ‖gradeZeroPiece x‖≤‖x‖ := by
  have h : ‖gradeZeroPiece x‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro word _
    by_cases g : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [gradeZeroPiece,g]
  nlinarith [norm_nonneg (gradeZeroPiece x),norm_nonneg x]

def gradeZeroProjection : H →L[ℂ] H :=
  (show H →ₗ[ℂ] H from {
    toFun := gradeZeroPiece
    map_add' := by
      intro x y
      apply PiLp.ext
      intro word
      by_cases g : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [gradeZeroPiece,g]
    map_smul' := by
      intro c x
      apply PiLp.ext
      intro word
      by_cases g : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [gradeZeroPiece,g] }).mkContinuous 1
        (fun x => by
          change ‖gradeZeroPiece x‖≤1*‖x‖
          simpa only [one_mul] using grade_zero_piece_bound x)

theorem grade_zero_projection_apply (x : H) (word : Occupation) :
    gradeZeroProjection x word = if (NativeHistoryGrade.sourceLabel word).2=0 then x word else 0 := rfl

theorem grade_zero_projection_pair (x y : H) :
    inner ℂ (gradeZeroProjection x) y=inner ℂ x (gradeZeroProjection y) := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  by_cases g : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [grade_zero_projection_apply,g]

theorem source_grade_apply (x : H) (word : Occupation) :
    GaussYukawaGrade.grade x word=((NativeHistoryGrade.sourceLabel word).2.val : ℂ) • x word := by
  simp [GaussYukawaGrade.grade,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,
    projection_apply,smul_ite,eq_comm]

theorem grade_zero_projected (x : H) : GaussYukawaGrade.grade (gradeZeroProjection x)=0 := by
  apply PiLp.ext
  intro word
  rw [source_grade_apply,grade_zero_projection_apply]
  by_cases g : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [g]

theorem grade_zero_fixed (x : H) (zeroGrade : GaussYukawaGrade.grade x=0) : gradeZeroProjection x=x := by
  apply PiLp.ext
  intro word
  rw [grade_zero_projection_apply]
  by_cases g : (NativeHistoryGrade.sourceLabel word).2=0
  · rw [if_pos g]
  · rw [if_neg g]
    have h := congrArg (fun v : H => v word) zeroGrade
    rw [source_grade_apply] at h
    change ((NativeHistoryGrade.sourceLabel word).2.val : ℂ) • x word=0 at h
    have hn : ((NativeHistoryGrade.sourceLabel word).2.val : ℂ)≠0 := by
      exact_mod_cast (show (NativeHistoryGrade.sourceLabel word).2.val≠0 from
        fun h => g (Fin.ext h))
    exact ((smul_eq_zero.mp h).resolve_left hn).symm

theorem grade_zero_resolution : gradeZeroProjection =
    ∑ g : Label, if g.2=0 then projection g else 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro word
  have each (g : Label) : (if g.2=0 then projection g else 0) x word =
      if NativeHistoryGrade.sourceLabel word=g then gradeZeroProjection x word else 0 := by
    by_cases equal : NativeHistoryGrade.sourceLabel word=g
    · subst g
      by_cases hz : (NativeHistoryGrade.sourceLabel word).2=0 <;>
        simp [hz,projection_apply,grade_zero_projection_apply]
    · by_cases hz : g.2=0 <;> simp [hz,projection_apply,equal]
  symm
  calc
    _ = ∑ g : Label, if NativeHistoryGrade.sourceLabel word=g then gradeZeroProjection x word else 0 := by
      simp only [sum_apply,WithLp.ofLp_sum,Finset.sum_apply]
      exact Finset.sum_congr rfl (fun g _ => each g)
    _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem grade_zero_commutes (A : H →L[ℂ] H) (preserves : ∀ g : Label, Commute (projection g) A) :
    Commute gradeZeroProjection A := by
  show gradeZeroProjection*A=A*gradeZeroProjection
  rw [grade_zero_resolution]
  simp only [Finset.sum_mul,Finset.mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
  apply Finset.sum_congr rfl
  intro g _
  rw [(preserves g).eq]

theorem grade_zero_cutoff (cut : ℕ) : gradeZeroProjection*cutoff cut=0 := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (gradeZeroProjection (cutoff cut y))=inner ℂ x 0
  rw [←grade_zero_projection_pair,inner_zero_right]
  apply positive_grade_pair_zero (cutoff cut) 1 (by omega) _ (gradeZeroProjection x) y (grade_zero_projected x)
  simpa only [Nat.cast_one,one_smul] using cutoff_raises cut

end LowEnergy.GaussComposite
