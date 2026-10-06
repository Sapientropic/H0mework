import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeGrade

/-! Full original Yukawa-cutoff evolution read by the source G=0 charged
composite endpoints. No equality of the full evolutions is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.GaussComposite
open GaussCoreHilbert GaussCoreDifferential NativeHistoryGrade GaussYukawaGrade
open FullYSourceCutoffVolterra
open GaussUnitaryHistory (HistorySpace sourceFilter inclusion)
open scoped InnerProductSpace BigOperators Topology
local instance labelFintypeCutoff : Fintype Label := Fintype.ofFinite _

theorem grade_symmetric : GaussYukawaGrade.grade.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (GaussYukawaGrade.grade x) y = inner ℂ x (GaussYukawaGrade.grade y)
  simp only [GaussYukawaGrade.grade, sum_apply, smul_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, map_natCast]
  exact Finset.sum_congr rfl (fun g _ => congrArg (fun z : ℂ => (g.2.val : ℂ)*z)
    (projection_symmetric g x y))

theorem positive_grade_pair_zero (T : H →L[ℂ] H) (n : ℕ) (positive : 0<n)
    (homogeneous : GaussYukawaGrade.grade*T=T*GaussYukawaGrade.grade+(n : ℂ) • T)
    (x y : H) (leftZero : GaussYukawaGrade.grade x=0) : inner ℂ x (T y)=0 := by
  have each (g : Label) : inner ℂ x (T (projection g y))=0 := by
    have hg := congrArg (fun A : H →L[ℂ] H => A y) (GaussYukawaInteraction.source_grade_right g)
    change GaussYukawaGrade.grade (projection g y)=(g.2.val : ℂ) • projection g y at hg
    have he := congrArg (fun A : H →L[ℂ] H => A (projection g y)) homogeneous
    change GaussYukawaGrade.grade (T (projection g y))=
      T (GaussYukawaGrade.grade (projection g y))+(n : ℂ) • T (projection g y) at he
    have pair := grade_symmetric x (T (projection g y))
    change inner ℂ (GaussYukawaGrade.grade x) (T (projection g y)) =
      inner ℂ x (GaussYukawaGrade.grade (T (projection g y))) at pair
    rw [leftZero, inner_zero_left, he, hg, map_smul, inner_add_right,
      inner_smul_right, inner_smul_right, ←add_mul] at pair
    have hn : (g.2.val : ℂ)+(n : ℂ) ≠ 0 := by
      rw [←Nat.cast_add]
      exact_mod_cast (show g.2.val+n≠0 by omega)
    exact (mul_eq_zero.mp pair.symm).resolve_left hn
  have hy : ∑ g : Label, projection g y=y := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun A : H →L[ℂ] H => A y) projection_resolution
  rw [←hy, map_sum, inner_sum]
  exact Finset.sum_eq_zero (fun g _ => each g)

theorem finite_cutoff_pair (cut : ℕ) (t : ℝ) (F : GaussUnitaryHistory.Index)
    (x y : H) (leftZero : GaussYukawaGrade.grade x=0) :
    inner ℂ x (SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t y)=
      inner ℂ x (SourceFiniteUnitary.time (GaussGradedCompression.compression F) t y) := by
  rw [←source_finite_evolution_return]
  have partialRead (n : ℕ) : inner ℂ x
      (partialEvolution (GaussGradedCompression.compression F) (cutoff cut) n t y)=
        inner ℂ x (SourceFiniteUnitary.time (GaussGradedCompression.compression F) t y) := by
    induction n with
    | zero => rw [partialEvolution]
    | succ n ih =>
      rw [partialEvolution, add_apply, inner_add_right, ih]
      have hz := positive_grade_pair_zero
        (finitePrefix (GaussGradedCompression.compression F) (cutoff cut) (n+1) t)
        (n+1) (by omega)
        (finitePrefix_homogeneous _ _ _ (source_compression_grade F) (cutoff_raises cut) (n+1) t)
        x y leftZero
      rw [hz,add_zero]
  exact partialRead 56

theorem source_cutoff_pair (cut : ℕ) (t : ℝ) (x y : H)
    (leftZero : GaussYukawaGrade.grade x=0) :
    inner ℂ (inclusion x) (sourceEvolution cut t (inclusion y))=
      inner ℂ (inclusion x) (GaussGradedUnitary.time t (inclusion y)) := by
  rw [sourceEvolution_inclusion, GaussGradedUnitary.time_inclusion]
  change inner ℂ ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
    (evolutionTrajectory cut t y : HistorySpace) =
    inner ℂ ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
      (GaussGradedUnitary.trajectory t y : HistorySpace)
  rw [SourceFamilyHilbert.inner_coe,SourceFamilyHilbert.inner_coe]
  unfold SourceFamilyHilbert.pair
  congr 1
  funext F
  exact finite_cutoff_pair cut t F x y leftZero

theorem composite_cutoff_pair (cut : ℕ) (t : ℝ)
    (leftAddition rightAddition : Bool) (a s b u : Fin 2) (f g : QuantumTest)
    (sourceGrade : gradeCore f=0) :
    inner ℂ (inclusion (leg leftAddition a s f))
      (sourceEvolution cut t (inclusion (leg rightAddition b u g))) =
    inner ℂ (inclusion (leg leftAddition a s f))
      (GaussGradedUnitary.time t (inclusion (leg rightAddition b u g))) := by
  apply source_cutoff_pair
  rw [leg_source_grade,sourceGrade,map_zero]

theorem composite_two_time (cut : ℕ) (s t : ℝ)
    (leftAddition rightAddition : Bool) (a u b v : Fin 2) (f g : QuantumTest)
    (sourceGrade : gradeCore f=0) :
    inner ℂ (sourceSharpEvolution cut s (inclusion (leg leftAddition a u f)))
      (sourceEvolution cut t (inclusion (leg rightAddition b v g))) =
    inner ℂ (inclusion (leg leftAddition a u f))
      (GaussGradedUnitary.time (t-s) (inclusion (leg rightAddition b v g))) := by
  rw [source_evolution_sharp_pair]
  have h := congrArg (fun A : HistorySpace →L[ℂ] HistorySpace =>
    A (inclusion (leg rightAddition b v g))) (sourceEvolution_add cut (-s) t)
  change sourceEvolution cut (-s+t) _ = sourceEvolution cut (-s) (sourceEvolution cut t _) at h
  rw [←h]
  simpa only [sub_eq_add_neg,add_comm] using
    composite_cutoff_pair cut (-s+t) leftAddition rightAddition a u b v f g sourceGrade

end LowEnergy.GaussComposite
