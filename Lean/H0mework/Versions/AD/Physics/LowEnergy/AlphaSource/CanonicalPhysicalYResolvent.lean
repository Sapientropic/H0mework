import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPhysicalResolvent
import Mathlib.Algebra.Ring.GeomSum

/-! The original positive Yukawa grade generates an exact finite resolvent
inverse on the whole carrier. No small-coupling or geometric-limit premise
is used; all full-Y terms are present before the original P10 observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalYResolvent
open GaussCoreHilbert GaussDiagonalHistory CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open CanonicalPhysicalResolvent (finiteResolvent finite_bound)
open CanonicalGradedCurrent (sourceProjection sourceLabel historyProjection)
open FullYSourceCutoffVolterra
open NativeHistoryGrade (Label projection)
open GaussUnitaryHistory (Index sourceFilter HistorySpace)
open SourceFamilyOperator
open scoped Topology InnerProductSpace
local instance labelFintype : Fintype Label := Fintype.ofFinite _

private theorem inverse_commutes {R : Type*} [Monoid R] (G D U : R)
    (left : U*D=1) (right : D*U=1) (commutes : G*D=D*G) : G*U=U*G := by
  calc
    G*U = (U*D)*(G*U) := by rw [left, one_mul]
    _ = U*(D*G)*U := by simp only [mul_assoc]
    _ = U*(G*D)*U := by rw [commutes]
    _ = (U*G)*(D*U) := by simp only [mul_assoc]
    _ = U*G := by rw [right, mul_one]

private theorem negative_product_raises {R : Type*} [Ring R] (G U Y : R)
    (commutes : G*U=U*G) (raises : G*Y=Y*G+Y) :
    G*(-(U*Y))=(-(U*Y))*G+(-(U*Y)) := by
  calc
    _ = -(U*(G*Y)) := by rw [mul_neg, ← mul_assoc, commutes, mul_assoc]
    _ = -(U*(Y*G+Y)) := by rw [raises]
    _ = _ := by simp only [mul_add, neg_add, neg_mul, mul_assoc]

private theorem inverse_factor {R : Type*} [Ring R] (D U Y : R) (right : D*U=1) :
    D+Y=D*(1-(-(U*Y))) := by
  rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, right, one_mul]

private theorem geometric_left {R : Type*} [Ring R] (D U N : R) (n : ℕ)
    (left : U*D=1) (nilpotent : N^n=0) :
    ((∑ i ∈ Finset.range n, N^i)*U)*(D*(1-N))=1 := by
  calc
    _ = (∑ i ∈ Finset.range n, N^i)*(U*D)*(1-N) := by simp only [mul_assoc]
    _ = 1 := by rw [left, mul_one, geom_sum_mul_neg, nilpotent, sub_zero]

private theorem geometric_right {R : Type*} [Ring R] (D U N : R) (n : ℕ)
    (right : D*U=1) (nilpotent : N^n=0) :
    (D*(1-N))*((∑ i ∈ Finset.range n, N^i)*U)=1 := by
  calc
    _ = D*((1-N)*(∑ i ∈ Finset.range n, N^i))*U := by simp only [mul_assoc]
    _ = 1 := by rw [mul_neg_geom_sum, nilpotent, sub_zero, mul_one, right]

theorem compression_grade (p : PhysicalMomentum) (F : Index) :
    Commute GaussYukawaGrade.grade (compression p F) := by
  change GaussYukawaGrade.grade*compression p F=compression p F*GaussYukawaGrade.grade
  simp only [GaussYukawaGrade.grade, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  exact Finset.sum_congr rfl (fun g _ => congrArg (fun T : H →L[ℂ] H => (g.2.val : ℂ) • T)
    (compression_blocks p F g).eq)

theorem resolvent_grade (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    Commute GaussYukawaGrade.grade (finiteResolvent p F z) := by
  have shifted := (compression_grade p F).sub_right
    ((Commute.one_right GaussYukawaGrade.grade).smul_right z)
  exact inverse_commutes _ _ _
    (FullYSourceResolventGraphSplice.resolvent_left _ (compression_selfAdjoint p F) z hz)
    (FullYSourceResolventGraphSplice.resolvent_right _ (compression_selfAdjoint p F) z hz) shifted.eq

def step (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) : H →L[ℂ] H :=
  -(finiteResolvent p F z*cutoff cut)

theorem step_raises (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    GaussYukawaGrade.grade*step p F cut z = step p F cut z*GaussYukawaGrade.grade+step p F cut z := by
  exact negative_product_raises _ _ _ (resolvent_grade p F z hz).eq (cutoff_raises cut)

theorem step_nilpotent (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    (step p F cut z)^57=0 := by
  have generated := FiniteGradeAlgebra.words_zero GaussYukawaGrade.grade projection
    (fun g : Label => (g.2.val : ℤ)) NativeHistoryGrade.projection_resolution
    (fun g => by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_left g)
    (fun g => by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_right g)
    0 56 (fun g => by have h := g.2.isLt; constructor <;> omega)
    (List.replicate 57 (step p F cut z))
    (fun T member => by
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp member
      exact step_raises p F cut z hz)
    (by simp)
  simpa only [List.prod_replicate] using generated

def series (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range 57, (step p F cut z)^n

def finiteFull (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) : H →L[ℂ] H :=
  series p F cut z*finiteResolvent p F z

theorem source_factor (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    compression p F+cutoff cut-z • 1 = (compression p F-z • 1)*(1-step p F cut z) := by
  have inverse := FullYSourceResolventGraphSplice.resolvent_right _ (compression_selfAdjoint p F) z hz
  change (compression p F-z • 1)*finiteResolvent p F z=1 at inverse
  have reorder : compression p F+cutoff cut-z • 1=(compression p F-z • 1)+cutoff cut := by abel
  exact reorder.trans (inverse_factor _ _ _ inverse)

theorem finiteFull_left (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    finiteFull p F cut z*(compression p F+cutoff cut-z • 1)=1 := by
  have inverse := FullYSourceResolventGraphSplice.resolvent_left _ (compression_selfAdjoint p F) z hz
  change finiteResolvent p F z*(compression p F-z • 1)=1 at inverse
  have generated := geometric_left (compression p F-z • 1) (finiteResolvent p F z)
    (step p F cut z) 57 inverse (step_nilpotent p F cut z hz)
  rw [← source_factor p F cut z hz] at generated
  exact generated

theorem finiteFull_right (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    (compression p F+cutoff cut-z • 1)*finiteFull p F cut z=1 := by
  have inverse := FullYSourceResolventGraphSplice.resolvent_right _ (compression_selfAdjoint p F) z hz
  change (compression p F-z • 1)*finiteResolvent p F z=1 at inverse
  have generated := geometric_right (compression p F-z • 1) (finiteResolvent p F z)
    (step p F cut z) 57 inverse (step_nilpotent p F cut z hz)
  rw [← source_factor p F cut z hz] at generated
  exact generated

theorem step_left_zero (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    sourceProjection*step p F cut z=0 :=
  CanonicalGradedCurrent.positive_grade_left_zero _ 1
    (by simpa only [Nat.cast_one, one_smul] using step_raises p F cut z hz) (by norm_num)

theorem power_left_zero (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (n : ℕ) (positive : 0<n) : sourceProjection*(step p F cut z)^n=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [pow_succ', ← mul_assoc, step_left_zero p F cut z hz, zero_mul]

theorem full_left_return (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    sourceProjection*finiteFull p F cut z=sourceProjection*finiteResolvent p F z := by
  have projected : sourceProjection*series p F cut z=sourceProjection := by
    rw [series, Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · rw [pow_zero, mul_one]
    · intro n _ different
      exact power_left_zero p F cut z hz n (Nat.pos_of_ne_zero different)
    · intro outside
      exact (outside (by simp)).elim
  rw [finiteFull, ← mul_assoc, projected]


def normBound (cut : ℕ) (z : ℂ) : ℝ :=
  (∑ n ∈ Finset.range 57, ((1/|z.im|)*‖cutoff cut‖)^n)*(1/|z.im|)

theorem normBound_nonneg (cut : ℕ) (z : ℂ) : 0≤normBound cut z := by
  unfold normBound
  positivity

theorem step_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    ‖step p F cut z‖ ≤ (1/|z.im|)*‖cutoff cut‖ := by
  rw [step, norm_neg]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (finite_bound p F z hz) (norm_nonneg _))

theorem power_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (n : ℕ) : ‖(step p F cut z)^n‖ ≤ ((1/|z.im|)*‖cutoff cut‖)^n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [one_apply_eq_self, one_mul, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ih (step_bound p F cut z hz) (norm_nonneg _) (by positivity))

theorem finiteFull_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    ‖finiteFull p F cut z‖ ≤ normBound cut z := by
  have seriesBound : ‖series p F cut z‖ ≤
      ∑ n ∈ Finset.range 57, ((1/|z.im|)*‖cutoff cut‖)^n := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => power_bound p F cut z hz n))
  exact (norm_mul_le _ _).trans
    (mul_le_mul seriesBound (finite_bound p F z hz) (norm_nonneg _) (by positivity))

def fullFamily (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0) : Operator Index H where
  component F := finiteFull p F cut z
  bounded := ⟨normBound cut z, normBound_nonneg cut z, fun F x =>
    ((finiteFull p F cut z).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteFull_bound p F cut z hz) (norm_nonneg x))⟩

def fullResolvent (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (fullFamily p cut z hz)

theorem fullResolvent_bound (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖fullResolvent p cut z hz x‖ ≤ normBound cut z*‖x‖ := by
  apply SourceBoundaryGram.lift_bound_explicit sourceFilter (fullFamily p cut z hz) _ (normBound_nonneg cut z)
  intro F g
  exact ((finiteFull p F cut z).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (finiteFull_bound p F cut z hz) (norm_nonneg g))

theorem completed_left_return (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    historyProjection*fullResolvent p cut z hz =
      historyProjection*CanonicalPhysicalResolvent.sourceResolvent p z hz := by
  change lift sourceFilter (constant sourceProjection)*lift sourceFilter (fullFamily p cut z hz) =
    lift sourceFilter (constant sourceProjection)*lift sourceFilter (CanonicalPhysicalResolvent.resolventFamily p z hz)
  calc
    _ = lift sourceFilter (comp (constant sourceProjection) (fullFamily p cut z hz)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (constant sourceProjection) (CanonicalPhysicalResolvent.resolventFamily p z hz)) :=
      lift_congr sourceFilter _ _ (fun F => full_left_return p F cut z hz)
    _ = _ := lift_comp sourceFilter _ _

theorem projected_cutoff_independent (p : PhysicalMomentum) (cut other : ℕ) (z : ℂ) (hz : z.im≠0) :
    historyProjection*fullResolvent p cut z hz=historyProjection*fullResolvent p other z hz := by
  rw [completed_left_return, completed_left_return]

theorem projection_bound (x : HistorySpace) : ‖historyProjection x‖ ≤ ‖x‖ := by
  have bound : ‖historyProjection x‖ ≤ 1*‖x‖ := by
    apply SourceBoundaryGram.lift_bound_explicit sourceFilter (constant sourceProjection) 1 zero_le_one
    intro F g
    simpa only [one_mul] using! NativeHistoryGrade.piece_bound sourceLabel g
  simpa only [one_mul] using bound

theorem projected_bound (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖historyProjection (fullResolvent p cut z hz x)‖ ≤ (1/|z.im|)*‖x‖ := by
  have returned := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x)
    (completed_left_return p cut z hz)
  change historyProjection (fullResolvent p cut z hz x)=
    historyProjection (CanonicalPhysicalResolvent.sourceResolvent p z hz x) at returned
  rw [returned]
  exact (projection_bound _).trans
    (CanonicalPhysicalResolvent.resolvent_bound p z hz x)

private theorem family_equal {f g : SourceFamilyHilbert.Family H sourceFilter}
    (equal : ∀ᶠ F in (sourceFilter : Filter Index),
      SourceFamilyHilbert.value f F=SourceFamilyHilbert.value g F) :
    (f : HistorySpace)=(g : HistorySpace) := by
  have nonpositive : ‖f-g‖ ≤ 0 := by
    apply SourceFamilyHilbert.norm_le_of_eventually sourceFilter (f-g) 0
    filter_upwards [equal] with F hF
    change ‖SourceFamilyHilbert.value f F-SourceFamilyHilbert.value g F‖ ≤ 0
    rw [hF, sub_self, norm_zero]
  have zero : ((f-g : SourceFamilyHilbert.Family H sourceFilter) : HistorySpace)=0 := by
    apply norm_eq_zero.mp
    rw [UniformSpace.Completion.norm_coe]
    exact le_antisymm nonpositive (norm_nonneg _)
  exact sub_eq_zero.mp (by simpa only [UniformSpace.Completion.coe_sub] using zero)

set_option maxRecDepth 8192 in
theorem full_shifted_core_return (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f : diagonal.domain) :
    fullResolvent p cut z hz (GaussUnitaryHistory.inclusion
      (physical p f+cutoff cut (f : H)-z • (f : H)))=GaussUnitaryHistory.inclusion (f : H) := by
  change lift sourceFilter (fullFamily p cut z hz)
    ((SourceFamilyHilbert.constant sourceFilter (physical p f+cutoff cut (f : H)-z • (f : H))) : HistorySpace) =
      ((SourceFamilyHilbert.constant sourceFilter (f : H)) : HistorySpace)
  rw [lift_coe]
  apply family_equal
  filter_upwards [eventually_exact p f] with F exactCore
  change finiteFull p F cut z (physical p f+cutoff cut (f : H)-z • (f : H))=(f : H)
  rw [← exactCore]
  exact congrArg (fun T : H →L[ℂ] H => T (f : H)) (finiteFull_left p F cut z hz)

end LowEnergy.CanonicalPhysicalYResolvent
