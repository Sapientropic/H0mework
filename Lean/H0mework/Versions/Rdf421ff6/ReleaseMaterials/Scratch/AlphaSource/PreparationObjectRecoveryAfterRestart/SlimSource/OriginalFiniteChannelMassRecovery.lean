import H0mework.Versions.Rdf421ff6.Physics.LowEnergy.Quantum.SourceJointResidualEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianSpectralMeasure
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] sourceBasis channel channelValue
private theorem channel_resolution (F : Index) (g : H) : ∑ i : Channel F,channel F i g=g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F g+(∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=g
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=((supportSpan F).orthogonalProjectionOnto g : H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

private theorem unit_projection_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v g : E) (hv : ‖v‖=1) :
    inner ℂ g ((inner ℂ v g) • v)=((‖(inner ℂ v g) • v‖^2 : ℝ) : ℂ) := by
  rw [inner_smul_right,norm_smul,hv,mul_one]
  rw [←inner_conj_symm g v]
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' (inner ℂ v g)

private theorem channel_pair (F : Index) (g : H) (i : Channel F) :
    inner ℂ g (channel F i g)=((‖channel F i g‖^2 : ℝ) : ℂ) := by
  cases i with
  | none =>
    have he : inner ℂ (escapeProjection F g) (supportProjection F g)=0 :=
      (supportSpan F).starProjection_inner_eq_zero g _ (Submodule.starProjection_apply_mem _ g)
    have hr : g=escapeProjection F g+supportProjection F g := by
      change g=(g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g
      abel
    simp only [channel]
    change inner ℂ g (escapeProjection F g)=_
    calc
      _ = inner ℂ (escapeProjection F g+supportProjection F g) (escapeProjection F g) :=
        congrArg (fun x : H => inner ℂ x (escapeProjection F g)) hr
      _ = _ := by
        rw [inner_add_left,inner_eq_zero_symm.mp he,add_zero]
        simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (escapeProjection F g)
  | some i =>
    have hs : channel F (some i) g=inner ℂ ((sourceBasis F) i : H) g • ((sourceBasis F) i : H) := by
      rw [channel,OrthonormalBasis.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    have hn : ‖((sourceBasis F) i : H)‖=1 := by
      change ‖(sourceBasis F) i‖=1
      exact (sourceBasis F).orthonormal.norm_eq_one i
    rw [hs]
    exact unit_projection_pair _ _ hn

/-- The full finite source spectrum has exactly the original input norm as its mass. -/
theorem actual_channel_mass (F : Index) (g : H) : ∑ i : Channel F,‖channel F i g‖^2=‖g‖^2 := by
  have h := congrArg (fun x : H => (inner ℂ g x).re) (channel_resolution F g)
  simp only [inner_sum,Complex.re_sum,channel_pair,Complex.ofReal_re] at h
  have hi : (inner ℂ g g).re=‖g‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) g).symm
  exact h.trans hi

end LowEnergy.SourceHamiltonianSpectralMeasure
