import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.SourceCausalGaussZero

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalSlowBlock
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy SourceRetardedIncrement
open PreparationVacuumPhysicalAbelZeroRead PreparationVacuumPhysicalCausalZeroRead
open PreparationVacuumPhysicalFeedback CanonicalPhysicalSpatial
open PreparationVacuumPhysicalHalfAxis
open scoped BigOperators InnerProductSpace Topology
attribute [local irreducible] actualC

def sourceChannelOp (F : GaussUnitaryHistory.Index) : Channel F→H→L[ℂ] H
  | none=>escapeProjection F
  | some i=>InnerProductSpace.rankOne ℂ ((sourceBasis F) i : H) ((sourceBasis F) i : H)

theorem sourceChannelOp_apply (F : GaussUnitaryHistory.Index) (i : Channel F) (x : H) :
    sourceChannelOp F i x=channel F i x := by
  cases i with
  | none=>rfl
  | some i=>
    simp only [sourceChannelOp,InnerProductSpace.rankOne_apply,channel,
      OrthonormalBasis.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

theorem sourceChannelOp_norm (F : GaussUnitaryHistory.Index) (i : Channel F) (x : H) :
    ‖sourceChannelOp F i x‖ ≤ ‖x‖ := by
  classical
  have bound:=Finset.single_le_sum (fun j (_ : j∈Finset.univ)=>sq_nonneg ‖channel F j x‖) (Finset.mem_univ i)
  rw [SourceHamiltonianSpectralMeasure.actual_channel_mass] at bound
  rw [sourceChannelOp_apply]
  nlinarith [norm_nonneg (channel F i x),norm_nonneg x]

theorem sourceChannelOp_price (F : GaussUnitaryHistory.Index) (i : Channel F) : ‖sourceChannelOp F i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using sourceChannelOp_norm F i x

theorem sourceChannelOp_resolution (F : GaussUnitaryHistory.Index) : ∑i : Channel F,sourceChannelOp F i=1 := by
  apply ContinuousLinearMap.ext
  intro x
  change (∑i : Channel F,sourceChannelOp F i) x=x
  simpa only [sum_apply,sourceChannelOp_apply] using source_channel_resolution F x

theorem sourceChannelOp_basis (F : GaussUnitaryHistory.Index) (i j : SpectralIndex F) :
    sourceChannelOp F (some i) ((sourceBasis F) j : H)=
      if i=j then ((sourceBasis F) j : H) else 0 := by
  classical
  simp only [sourceChannelOp,InnerProductSpace.rankOne_apply]
  change inner ℂ ((sourceBasis F) i) ((sourceBasis F) j) • ((sourceBasis F) i : H)=_
  rw [(sourceBasis F).inner_eq_ite]
  split_ifs with same
  · subst j
    simp only [one_smul]
  · simp only [zero_smul]

theorem sourceChannelOp_left (F : GaussUnitaryHistory.Index) (i : Channel F) :
    actualC 0 F*sourceChannelOp F i=(channelValue F i : ℂ) • sourceChannelOp F i := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,smul_apply,sourceChannelOp_apply]
  exact source_channel_eigen F i x

theorem sourceChannelOp_right (F : GaussUnitaryHistory.Index) (i : Channel F) :
    sourceChannelOp F i*actualC 0 F=(channelValue F i : ℂ) • sourceChannelOp F i := by
  apply ContinuousLinearMap.ext
  intro x
  cases i with
  | none=>
    simp only [sourceChannelOp,mul_apply_eq_comp,smul_apply,channelValue,Complex.ofReal_zero,zero_smul]
    rw [sourceC0_generated]
    exact escape_compression_zero F x
  | some i=>
    have eigen:actualC 0 F ((sourceBasis F) i : H)=(channelValue F (some i) : ℂ) • ((sourceBasis F) i : H) := by
      have h:=source_channel_eigen F (some i) ((sourceBasis F) i : H)
      rw [←sourceChannelOp_apply,sourceChannelOp_basis,if_pos rfl] at h
      exact h
    have pair:inner ℂ (actualC 0 F ((sourceBasis F) i : H)) x=
        inner ℂ ((sourceBasis F) i : H) (actualC 0 F x) := by
      rw [sourceC0_generated]
      exact GaussGradedCompression.compression_pair F _ _
    simp only [sourceChannelOp,mul_apply_eq_comp,InnerProductSpace.rankOne_apply,smul_apply]
    rw [←pair,eigen]
    simp only [inner_smul_left,Complex.conj_ofReal,smul_smul]

private theorem escape_basis (F : GaussUnitaryHistory.Index) (i : SpectralIndex F) :
    escapeProjection F ((sourceBasis F) i : H)=0 := by
  change ((sourceBasis F) i : H)-(supportSpan F).starProjection ((sourceBasis F) i : H)=0
  rw [Submodule.starProjection_eq_self_iff.mpr ((sourceBasis F) i).property,sub_self]

private theorem basis_escape (F : GaussUnitaryHistory.Index) (i : SpectralIndex F) (x : H) :
    inner ℂ ((sourceBasis F) i : H) (escapeProjection F x)=0 := by
  exact inner_eq_zero_symm.mp ((supportSpan F).starProjection_inner_eq_zero x _ ((sourceBasis F) i).property)

private theorem complement_idempotent {B : Type*} [Ring B] (P : B) (idempotent : P*P=P) :
    (1-P)*(1-P)=1-P := by
  calc
    _=1-P-P+P*P := by noncomm_ring
    _=1-P := by rw [idempotent];abel

theorem sourceChannelOp_product (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourceChannelOp F i*sourceChannelOp F j=if i=j then sourceChannelOp F i else 0 := by
  classical
  cases i with
  | none=>
    cases j with
    | none=>
      simp only [if_true,sourceChannelOp]
      have projection:supportProjection F*supportProjection F=supportProjection F := by
        apply ContinuousLinearMap.ext
        intro x
        change (supportSpan F).starProjection ((supportSpan F).starProjection x)=(supportSpan F).starProjection x
        exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ x)
      exact complement_idempotent _ projection
    | some j=>
      simp only [reduceCtorEq,if_false,sourceChannelOp]
      apply ContinuousLinearMap.ext
      intro x
      simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul,escape_basis,smul_zero,zero_apply]
  | some i=>
    cases j with
    | none=>
      simp only [reduceCtorEq,if_false,sourceChannelOp]
      apply ContinuousLinearMap.ext
      intro x
      simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,basis_escape,zero_smul,zero_apply]
    | some j=>
      apply ContinuousLinearMap.ext
      intro x
      simp only [mul_apply_eq_comp,sourceChannelOp,InnerProductSpace.rankOne_apply,inner_smul_right]
      change (inner ℂ ((sourceBasis F) j : H) x*inner ℂ ((sourceBasis F) i) ((sourceBasis F) j)) • ((sourceBasis F) i : H)=_
      rw [(sourceBasis F).inner_eq_ite]
      by_cases same:i=j
      · subst j
        simp only [if_true,mul_one,InnerProductSpace.rankOne_apply]
      · simp only [mul_zero,zero_smul,Option.some.injEq,same,if_false,zero_apply]

end LowEnergy.PreparationVacuumPhysicalSlowBlock
