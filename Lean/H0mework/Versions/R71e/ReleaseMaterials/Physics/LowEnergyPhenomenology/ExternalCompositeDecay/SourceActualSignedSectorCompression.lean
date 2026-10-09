import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualSignedSectorAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSignedSector
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open Filter
open scoped InnerProductSpace Topology BigOperators

/-- This is still an element of the original source-core domain. -/
def corePiece (s : ℝ) (x : diagonal.domain) : diagonal.domain :=
  ⟨projection s (x : H),stable s x⟩

theorem corePiece_idempotent (s : ℝ) (x : diagonal.domain) :
    corePiece s (corePiece s x) = corePiece s x := Subtype.ext (projection_idempotent s x)

/-- Saturate the actual finite source columns, without changing the source index carrier. -/
def saturate (s : ℝ) (F : Index) : Index := by
  classical
  exact F ∪ F.image (corePiece s)

theorem saturate_contains (s : ℝ) (F : Index) : F ≤ saturate s F := by
  classical
  exact Finset.subset_union_left

theorem saturate_closed (s : ℝ) (F : Index) (x : diagonal.domain) (hx : x ∈ saturate s F) :
    corePiece s x ∈ saturate s F := by
  classical
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    rw [corePiece_idempotent]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)

theorem saturate_cofinal (s : ℝ) :
    Tendsto (saturate s) (sourceFilter : Filter Index) atTop :=
  Filter.tendsto_atTop_mono (saturate_contains s)
    (show Tendsto (fun F : Index => F) (sourceFilter : Filter Index) atTop from
      WeakCoreEvolution.sourceFilter_cofinal diagonal)

private theorem span_stable (s : ℝ) (F : Index) (x : H)
    (hx : x ∈ FiniteCoreEvolution.coreSpan diagonal (saturate s F)) :
    projection s x ∈ FiniteCoreEvolution.coreSpan diagonal (saturate s F) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y,hy,rfl⟩ := hx
    exact FiniteCoreEvolution.mem_coreSpan diagonal (saturate s F) (corePiece s y)
      (saturate_closed s F y hy)
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

private theorem span_projection (s : ℝ) (F : Index) (x : H) :
    (FiniteCoreEvolution.coreSpan diagonal (saturate s F)).starProjection (projection s x) =
      projection s ((FiniteCoreEvolution.coreSpan diagonal (saturate s F)).starProjection x) := by
  let S := FiniteCoreEvolution.coreSpan diagonal (saturate s F)
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact span_stable s F _ (S.starProjection_apply_mem x)
  · intro w hw
    rw [←map_sub]
    exact (projection_symmetric s _ w).trans
      (S.starProjection_inner_eq_zero x (projection s w) (span_stable s F w hw))

/-- The old finite source compression itself now commutes; no new compressed operator is defined. -/
theorem actual_finite_compression (s : ℝ) (F : Index) :
    Commute (projection s) (FiniteCoreEvolution.compression diagonal (saturate s F)) := by
  let S := FiniteCoreEvolution.coreSpan diagonal (saturate s F)
  let px (x : H) : diagonal.domain :=
    ⟨S.starProjection x,FiniteCoreEvolution.coreSpan_le diagonal (saturate s F) (S.starProjection_apply_mem x)⟩
  have formula (x : H) : FiniteCoreEvolution.compression diagonal (saturate s F) x =
      S.starProjection (diagonal (px x)) := rfl
  have relation (x : H) : px (projection s x) = corePiece s (px x) :=
    Subtype.ext (span_projection s F x)
  show _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro x
  change projection s (FiniteCoreEvolution.compression diagonal (saturate s F) x) =
    FiniteCoreEvolution.compression diagonal (saturate s F) (projection s x)
  rw [formula,formula,relation]
  have hd := diagonal_commutes s (px x)
  change diagonal (corePiece s (px x)) = projection s (diagonal (px x)) at hd
  rw [hd]
  exact (span_projection s F _).symm

/-- The original Number/grade compressed Hamiltonian retains the signed sector
on the explicitly generated common cofinal range of source finite sets. -/
theorem actual_graded_compression (s : ℝ) (F : Index) :
    Commute (projection s) (GaussGradedCompression.compression (saturate s F)) := by
  unfold GaussGradedCompression.compression
  apply Commute.sum_right
  intro g _
  exact ((projection_grade s g).mul_right (actual_finite_compression s F)).mul_right (projection_grade s g)

end LowEnergy.ActualSignedSector
