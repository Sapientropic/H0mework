import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalCompletedSectorGraph

/-! The unchanged finite Galerkin resolvent exactly consumes original shifted
core sources. Canonical cross return therefore factors through the actual
deficiency input, with the same positive-frequency bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.CanonicalCompletedSector
open GaussCoreHilbert GaussDiagonalHistory SourceMinimalGraphParticular SourceBoundaryGram
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open FullYSourceResolventGraphSplice SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace

private theorem family_equal {f g : Family H sourceFilter}
    (equal : ∀ᶠ F in (sourceFilter : Filter Index), value f F = value g F) :
    (f : HistorySpace) = (g : HistorySpace) := by
  have hn : ‖f-g‖ ≤ 0 := by
    apply norm_le_of_eventually sourceFilter (f-g) 0
    filter_upwards [equal] with F hF
    change ‖value f F-value g F‖≤0
    rw [hF,sub_self,norm_zero]
  have hz : ((f-g : Family H sourceFilter) : HistorySpace)=0 := by
    apply norm_eq_zero.mp
    rw [UniformSpace.Completion.norm_coe]
    exact le_antisymm hn (norm_nonneg _)
  exact sub_eq_zero.mp (by simpa only [UniformSpace.Completion.coe_sub] using hz)

theorem same_resolvent_shifted_core (z : ℂ) (hz : z.im≠0) (f : diagonal.domain) :
    sameResolvent z hz (inclusion (shift diagonal z f)) = inclusion (f : H) := by
  change lift sourceFilter (resolventFamily z hz)
    ((SourceFamilyHilbert.constant sourceFilter (shift diagonal z f)) : HistorySpace) =
    ((SourceFamilyHilbert.constant sourceFilter (f : H)) : HistorySpace)
  rw [lift_coe]
  apply family_equal
  filter_upwards [GaussGradedCompression.eventually_exact f] with F hF
  change finiteResolvent F z (diagonal f-z • (f : H))=(f : H)
  rw [←hF]
  exact congrArg (fun A : H →L[ℂ] H => A (f : H))
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)

def sourceCross (z : ℂ) (hz : z.im≠0) : H →L[ℂ] HistorySpace :=
  ((1-completedProjection)*sameResolvent z hz).comp (sourceInclusion.comp projection)

theorem sourceCross_apply (z : ℂ) (hz : z.im≠0) (x : H) :
    sourceCross z hz x = (sameResolvent z hz (inclusion (projection x))-
      completedProjection (sameResolvent z hz (inclusion (projection x)))) := rfl

theorem projection_twice (x : H) : projection (projection x) = projection x :=
  congrArg (fun A : H →L[ℂ] H => A x) projection_idempotent

theorem sourceCross_shifted_core (z : ℂ) (hz : z.im≠0) (f : diagonal.domain) :
    sourceCross z hz (shift diagonal z f)=0 := by
  rw [sourceCross_apply,shifted_core,same_resolvent_shifted_core,
    completed_projection_inclusion]
  change inclusion (projection (f : H))-inclusion (projection (projection (f : H)))=0
  rw [projection_twice,sub_self]

theorem sourceCross_shifted_range (z : ℂ) (hz : z.im≠0) {x : H}
    (hx : x ∈ shiftedRange diagonal z) : sourceCross z hz x=0 := by
  have h : Set.EqOn (fun x => sourceCross z hz x) (fun _ => 0)
      (LinearMap.range (shift diagonal z) : Set H) := by
    rintro y ⟨f,rfl⟩
    exact sourceCross_shifted_core z hz f
  exact h.closure (sourceCross z hz).continuous continuous_const hx

theorem sourceCross_deficiency (z : ℂ) (hz : z.im≠0) (x : H) :
    sourceCross z hz x=sourceCross z hz (sourceDefect z x) := by
  change sourceCross z hz x=sourceCross z hz (x-(shiftedRange diagonal z).starProjection x)
  rw [map_sub,sourceCross_shifted_range z hz ((shiftedRange diagonal z).starProjection_apply_mem x),sub_zero]

theorem completed_complement_bound (x : HistorySpace) :
    ‖x-completedProjection x‖≤‖x‖ := by
  have hs : completedProjection (completedProjection x)=completedProjection x :=
    congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A x) completed_projection_square
  have hp : inner ℂ (completedProjection x) (x-completedProjection x)=0 := by
    rw [completed_projection_inner,map_sub,hs,sub_self,inner_zero_right]
  have he : completedProjection x+(x-completedProjection x)=x := by abel
  have hn := norm_add_sq (𝕜 := ℂ) (completedProjection x) (x-completedProjection x)
  rw [he,hp] at hn
  simp only [map_zero,mul_zero,add_zero] at hn
  nlinarith [sq_nonneg ‖completedProjection x‖,norm_nonneg (x-completedProjection x),norm_nonneg x]

theorem sourceCross_deficiency_bound (z : ℂ) (hz : z.im≠0) (x : H) :
    ‖sourceCross z hz x‖ ≤ (1/|z.im|)*‖projection (sourceDefect z x)‖ := by
  rw [sourceCross_deficiency z hz x,sourceCross_apply]
  apply (completed_complement_bound _).trans
  simpa only [inclusion.norm_map] using same_resolvent_bound z hz
    (inclusion (projection (sourceDefect z x)))

theorem original_source_zero_of_deficiency_zero (z : ℂ) (hz : z.im≠0) (x : H)
    (zero : projection (sourceDefect z x)=0) : sourceCross z hz x=0 := by
  have h := sourceCross_deficiency_bound z hz x
  rw [zero,norm_zero,mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

#print axioms same_resolvent_shifted_core
#print axioms sourceCross_shifted_range
#print axioms sourceCross_deficiency
#print axioms sourceCross_deficiency_bound
end LowEnergy.CanonicalCompletedSector
