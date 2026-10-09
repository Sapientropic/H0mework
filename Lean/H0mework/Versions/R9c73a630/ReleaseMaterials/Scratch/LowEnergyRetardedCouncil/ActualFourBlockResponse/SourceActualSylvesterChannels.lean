import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointCost
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceHamiltonianSpectralMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualSylvesterChannels
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open FullYSourceResolventGraphSplice SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement
open scoped BigOperators InnerProductSpace

theorem basis_eigen (F : Index) (i : SpectralIndex F) :
    GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : H)=
      (channelValue F (some i) : ℂ) • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  have h := (show (supportAction F).toLinearMap.IsSymmetric from
    (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
  simpa only [SourceJointResidualEnergy.sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
    SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun x : supportSpan F => (x : H)) h

theorem channel_some (F : Index) (i : SpectralIndex F) (x : H) :
    channel F (some i) x=inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  change (SourceJointResidualEnergy.sourceBasis F).repr
    ((supportSpan F).orthogonalProjectionOnto x) i • _=_
  apply congrArg (fun c : ℂ => c • ((SourceJointResidualEnergy.sourceBasis F) i : H))
  exact ((SourceJointResidualEnergy.sourceBasis F).repr_apply_apply _ _).trans
    (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ((SourceJointResidualEnergy.sourceBasis F) i) x)

theorem eigen_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (C : E →L[ℂ] E) (v x : E) (a : ℝ)
    (hp : inner ℂ v (C x)=inner ℂ (C v) x) (he : C v=(a : ℂ) • v) :
    inner ℂ v (C x)=(a : ℂ)*inner ℂ v x := by
  rw [hp,he,inner_smul_left,Complex.conj_ofReal]

theorem channel_eigen_right (F : Index) (i : Channel F) (x : H) :
    GaussGradedCompression.compression F (channel F i x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using compression_escape_zero F x
  | some i =>
    rw [channel_some,map_smul,basis_eigen]
    exact smul_comm _ _ _

theorem channel_eigen_left (F : Index) (i : Channel F) (x : H) :
    channel F i (GaussGradedCompression.compression F x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using escape_compression_zero F x
  | some i =>
    have hp : inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H)
        (GaussGradedCompression.compression F x)=
        inner ℂ (GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : H)) x := by
      simpa only using! (GaussGradedCompression.compression_pair F
        ((SourceJointResidualEnergy.sourceBasis F) i : H) x).symm
    have he := eigen_inner (E := H) (GaussGradedCompression.compression F)
      ((SourceJointResidualEnergy.sourceBasis F) i : H) x (channelValue F (some i)) hp (basis_eigen F i)
    calc
      _=inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H)
          (GaussGradedCompression.compression F x) • ((SourceJointResidualEnergy.sourceBasis F) i : H) :=
        channel_some F i _
      _=((channelValue F (some i) : ℂ)*inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x) •
          ((SourceJointResidualEnergy.sourceBasis F) i : H) := congrArg (fun c : ℂ => c • _) he
      _=(channelValue F (some i) : ℂ) •
          (inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x • ((SourceJointResidualEnergy.sourceBasis F) i : H)) :=
        (smul_smul _ _ _).symm
      _=_ := congrArg (fun y : H => (channelValue F (some i) : ℂ) • y) (channel_some F i x).symm


/-- The escape projector remains an actual channel on the entire Hilbert space. -/
def projection (F : Index) : Channel F → H →L[ℂ] H
  | none => escapeProjection F
  | some i => InnerProductSpace.rankOne ℂ ((sourceBasis F) i : H) ((sourceBasis F) i : H)

theorem projection_apply (F : Index) (i : Channel F) (x : H) :
    projection F i x = channel F i x := by
  cases i with
  | none => rfl
  | some i => exact (channel_some F i x).symm

theorem channel_resolution (F : Index) (g : H) : ∑ i : Channel F, channel F i g = g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F g + (∑ i,(sourceBasis F).repr
    ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H)) = g
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i •
    ((sourceBasis F) i : H)) = ((supportSpan F).orthogonalProjectionOnto g : H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

theorem channel_orthogonal (F : Index) (i k : Channel F) (h : i ≠ k) (x y : H) :
    inner ℂ (channel F i x) (channel F k y) = 0 := by
  cases i with
  | none =>
    cases k with
    | none => exact (h rfl).elim
    | some k =>
      rw [channel_some,inner_smul_right]
      have hz : inner ℂ (escapeProjection F x) ((sourceBasis F) k : H) = 0 :=
        (supportSpan F).starProjection_inner_eq_zero x _ ((sourceBasis F) k).property
      simp only [channel,hz,mul_zero]
  | some i =>
    cases k with
    | none =>
      rw [channel_some,inner_smul_left]
      have hz : inner ℂ (escapeProjection F y) ((sourceBasis F) i : H) = 0 :=
        (supportSpan F).starProjection_inner_eq_zero y _ ((sourceBasis F) i).property
      change _ * inner ℂ ((sourceBasis F) i : H) (escapeProjection F y) = 0
      rw [inner_eq_zero_symm.mp hz,mul_zero]
    | some k =>
      rw [channel_some,channel_some,inner_smul_left,inner_smul_right]
      have hik : i ≠ k := fun e => h (congrArg some e)
      have hz : inner ℂ ((sourceBasis F) i : H) ((sourceBasis F) k : H) = 0 := by
        exact (sourceBasis F).orthonormal.inner_eq_zero hik
      rw [hz,mul_zero,mul_zero]

theorem leg_orthogonal (F : Index) (D : H →L[ℂ] H) (g : H)
    (i j k l : Channel F) (hik : i ≠ k) :
    inner ℂ (spectralLeg F D g (i,j)) (spectralLeg F D g (k,l)) = 0 :=
  channel_orthogonal F i k hik _ _

end LowEnergy.ActualSylvesterChannels
