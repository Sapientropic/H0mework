import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalCompletedSectorCore
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceBoundaryGram

/-! The actual source projection reduces the original minimal and adjoint
graphs. Its existing completed-time leakage is kept in the same boundary return. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalCompletedSector
open GaussCoreHilbert GaussDiagonalHistory SymmetricGraphClosure
open SourceMinimalGraphParticular SourceBoundaryGram
open GaussUnitaryHistory (HistorySpace inclusion reader)
open FullYSourceResolventGraphSplice
open scoped Topology InnerProductSpace

theorem projection_inner (x y : H) :
    inner ℂ (projection x) y = inner ℂ x (projection y) := projection_symmetric x y

theorem closed_graph_project {p : H × H} (hp : p ∈ closedGraph diagonal) :
    (projection p.1,projection p.2) ∈ closedGraph diagonal := by
  let P := projection.prodMap projection
  let K := (closedGraph diagonal).comap P.toLinearMap
  have hc : IsClosed (K : Set (H × H)) :=
    diagonal.graph.isClosed_topologicalClosure.preimage P.continuous
  have hi : diagonal.graph ≤ K := by
    intro pair hpair
    obtain ⟨f,rfl⟩ := diagonal.mem_graph_iff'.mp hpair
    change (projection (f : H),projection (diagonal f)) ∈ closedGraph diagonal
    rw [←diagonal_commutes]
    exact diagonal.graph.le_topologicalClosure (diagonal.mem_graph ⟨projection (f : H),stable f⟩)
  exact diagonal.graph.topologicalClosure_minimal hi hc hp

theorem adjoint_graph_project {p : H × H} (hp : p ∈ GaussAdjointHistory.graph) :
    (projection p.1,projection p.2) ∈ GaussAdjointHistory.graph := by
  intro d
  change inner ℂ (projection p.1) (diagonal d) = inner ℂ (projection p.2) (d : H)
  rw [projection_inner,←diagonal_commutes, hp ⟨projection (d : H),stable d⟩,
    projection_inner]

def coreProject (f : diagonal.domain) : diagonal.domain := ⟨projection (f : H),stable f⟩

theorem shifted_core (w : ℂ) (f : diagonal.domain) :
    projection (shift diagonal w f) = shift diagonal w (coreProject f) := by
  change projection (diagonal f-w • (f : H)) =
    diagonal (coreProject f)-w • projection (f : H)
  rw [map_sub,map_smul,←diagonal_commutes]
  rfl

theorem shiftedRange_project (w : ℂ) {x : H} (hx : x ∈ shiftedRange diagonal w) :
    projection x ∈ shiftedRange diagonal w := by
  let R := shiftedRange diagonal w
  let K := R.comap projection.toLinearMap
  have hc : IsClosed (K : Set H) :=
    (LinearMap.range (shift diagonal w)).isClosed_topologicalClosure.preimage projection.continuous
  have hi : LinearMap.range (shift diagonal w) ≤ K := by
    rintro y ⟨f,rfl⟩
    change projection (shift diagonal w f) ∈ shiftedRange diagonal w
    rw [shifted_core]
    exact (LinearMap.range (shift diagonal w)).le_topologicalClosure
      (LinearMap.mem_range_self _ (coreProject f))
  exact (LinearMap.range (shift diagonal w)).topologicalClosure_minimal hi hc hx

theorem shiftedRange_orthogonal (w : ℂ) {x : H} (hx : x ∈ (shiftedRange diagonal w)ᗮ) :
    projection x ∈ (shiftedRange diagonal w)ᗮ := by
  intro y hy
  rw [←projection_inner]
  exact hx _ (shiftedRange_project w hy)

theorem shiftedRange_commutes (w : ℂ) :
    Commute projection (shiftedRange diagonal w).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  change projection ((shiftedRange diagonal w).starProjection x) =
    (shiftedRange diagonal w).starProjection (projection x)
  symm
  apply (shiftedRange diagonal w).eq_starProjection_of_mem_orthogonal
  · exact shiftedRange_project w ((shiftedRange diagonal w).starProjection_apply_mem x)
  · rw [←map_sub]
    exact shiftedRange_orthogonal w ((shiftedRange diagonal w).sub_starProjection_mem_orthogonal x)

def rangeProject (w : ℂ) : shiftedRange diagonal w →L[ℂ] shiftedRange diagonal w :=
  (projection.comp (shiftedRange diagonal w).subtypeL).codRestrict _
    (fun x => shiftedRange_project w x.property)

theorem rangeProject_core (w : ℂ) (f : diagonal.domain) :
    rangeProject w (intoShiftedRange diagonal w f) =
      intoShiftedRange diagonal w (coreProject f) := Subtype.ext (shifted_core w f)

theorem inverse_range_commutes (w : ℂ) (hw : w.im≠0) (x : shiftedRange diagonal w) :
    projection (inverseOnRange diagonal w x) = inverseOnRange diagonal w (rangeProject w x) := by
  refine (intoShiftedRange_dense diagonal w).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [rangeProject_core,inverseOnRange_core diagonal diagonal_pair w hw,
    inverseOnRange_core diagonal diagonal_pair w hw]
  rfl

theorem particular_commutes (w : ℂ) (hw : w.im≠0) :
    Commute projection (sourceParticular w) := by
  apply ContinuousLinearMap.ext
  intro x
  change projection (inverseOnRange diagonal w ((shiftedRange diagonal w).orthogonalProjectionOnto x)) =
    inverseOnRange diagonal w ((shiftedRange diagonal w).orthogonalProjectionOnto (projection x))
  rw [inverse_range_commutes w hw]
  congr 1
  apply Subtype.ext
  exact congrArg (fun A : H →L[ℂ] H => A x) (shiftedRange_commutes w).eq

theorem defect_commutes (w : ℂ) : Commute projection (sourceDefect w) := by
  exact (Commute.one_right projection).sub_right (shiftedRange_commutes w)

theorem max_particular_commutes (z : ℂ) (hz : z.im≠0) : Commute projection (maxParticular z) := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have h := congrArg star (particular_commutes (star z) hs).eq
  have hp : star projection = projection := projection_symmetric.isSelfAdjoint
  simp only [star_mul,hp] at h
  exact h.symm

def completedProjection : HistorySpace →L[ℂ] HistorySpace := reader projection

theorem completed_projection_inclusion (x : H) :
    completedProjection (inclusion x) = inclusion (projection x) :=
  GaussUnitaryHistory.reader_inclusion projection x

theorem completed_projection_inner (x y : HistorySpace) :
    inner ℂ (completedProjection x) y = inner ℂ x (completedProjection y) :=
  SourceFamilyOperator.lift_pair GaussUnitaryHistory.sourceFilter
    (SourceFamilyOperator.constant projection) (SourceFamilyOperator.constant projection)
    (fun _ a b => projection_inner a b) x y

theorem sourceSeen_project (x : HistorySpace) : sourceSeen (completedProjection x) = projection (sourceSeen x) := by
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (sourceSeen (completedProjection x)) =
        inner ℂ (sourceInclusion y) (completedProjection x) :=
      ContinuousLinearMap.adjoint_inner_right sourceInclusion y (completedProjection x)
    _ = inner ℂ (completedProjection (inclusion y)) x :=
      (completed_projection_inner (inclusion y) x).symm
    _ = inner ℂ (sourceInclusion (projection y)) x := by rw [completed_projection_inclusion]; rfl
    _ = inner ℂ (projection y) (sourceSeen x) :=
      (ContinuousLinearMap.adjoint_inner_right sourceInclusion (projection y) x).symm
    _ = inner ℂ y (projection (sourceSeen x)) := projection_inner y (sourceSeen x)

theorem body_commutes (z : ℂ) (hz : z.im≠0) : Commute completedProjection (sourceBody z) := by
  apply ContinuousLinearMap.ext
  intro x
  change completedProjection (inclusion (maxParticular z (sourceSeen x))) =
    inclusion (maxParticular z (sourceSeen (completedProjection x)))
  rw [completed_projection_inclusion,sourceSeen_project]
  exact congrArg inclusion (congrArg (fun A : H →L[ℂ] H => A (sourceSeen x))
    (max_particular_commutes z hz).eq)

theorem completed_projection_square : completedProjection * completedProjection = completedProjection := by
  rw [completedProjection,←GaussUnitaryHistory.reader_mul,projection_idempotent]

private theorem cross_algebra {R : Type*} [Ring R] (p r b : R)
    (hp : p*p=p) (hb : p*b=b*p) : (1-p)*r*p=(1-p)*(r-b)*p := by
  have hz : (1-p)*b*p=0 := by
    rw [mul_assoc,←hb,←mul_assoc,sub_mul,one_mul,hp,sub_self,zero_mul]
  calc
    (1-p)*r*p = (1-p)*r*p-(1-p)*b*p := by rw [hz,sub_zero]
    _ = ((1-p)*r-(1-p)*b)*p := (sub_mul _ _ _).symm
    _ = (1-p)*(r-b)*p := congrArg (fun x : R => x*p) (mul_sub (1-p) r b).symm

theorem actual_cross_boundary (z : ℂ) (hz : z.im≠0) :
    (1-completedProjection)*sameResolvent z hz*completedProjection =
      (1-completedProjection)*boundaryReturn z hz*completedProjection := by
  exact cross_algebra completedProjection (sameResolvent z hz) (sourceBody z)
    completed_projection_square (body_commutes z hz).eq

#print axioms closed_graph_project
#print axioms particular_commutes
#print axioms actual_cross_boundary
end LowEnergy.CanonicalCompletedSector
