import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventSylvester
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherChannelGap
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarPairedTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualSylvesterCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceJointResidualEnergy SourceRetardedIncrement
open ActualSylvesterChannels ActualSylvesterKernels ActualTwoResolventSylvester
open SourceInverseNoetherChannelGap SourceScalarPairedTransport SourceCutoffDilationWard
open scoped BigOperators InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem core_embed (f : QuantumTest) : (coreEquiv f : H) = embed f := rfl
private theorem channelTest_embed (F : Index) (i : Channel F) (g : diagonal.domain) :
    embed (channelTest F g i) = channel F i (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

def channelCore (F : Index) (i : Channel F) : End where
  toFun f := channelTest F (coreEquiv f) i
  map_add' f g := by
    apply embed_injective
    simp only [map_add,channelTest_embed,Submodule.coe_add,core_embed]
    rw [←projection_apply,map_add,projection_apply,projection_apply]
  map_smul' c f := by
    apply embed_injective
    simp only [map_smul,channelTest_embed,Submodule.coe_smul,core_embed,RingHom.id_apply]
    rw [←projection_apply,map_smul,projection_apply]

theorem actual_channel_core (F : Index) (i : Channel F) (f : QuantumTest) :
    embed (channelCore F i f) = channel F i (embed f) := channelTest_embed F i (coreEquiv f)

/-- Both exact causal smoothings remain on the original test core, before applying any source form. -/
def sourceLCore (advanced sharp : Bool) (F : Index) (μ : ℝ) (m ell : ℕ) : End :=
  ∑ij : Channel F × Channel F,
    coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) •
      ((channelCore F ij.1 * literalIncrementAction sharp m ell) * channelCore F ij.2)

theorem actual_source_L_core (advanced sharp : Bool) (F : Index) (μ : ℝ) (m ell : ℕ)
    (f : QuantumTest) :
    embed (sourceLCore advanced sharp F μ m ell f) =
      sourceL advanced F μ (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed f) := by
  rw [actual_source_L]
  simp only [sourceLCore,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    map_sum,map_smul,actual_channel_core,←literal_increment_core,spectralLeg]

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f) = GaussGradedCompression.compression F (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The full original source core receives the actual CF Sylvester equation, not an H0 replacement. -/
theorem actual_source_core_sylvester (advanced sharp : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (m ell : ℕ) (f : QuantumTest) :
    (2*(μ : ℂ)) • sourceLCore advanced sharp F μ m ell f -
      (Complex.I*(if advanced then -1 else 1)) •
        (compressionCore F (sourceLCore advanced sharp F μ m ell f) -
          sourceLCore advanced sharp F μ m ell (compressionCore F f)) = literalIncrementAction sharp m ell f := by
  apply embed_injective
  have hs := congrArg (fun A : H →L[ℂ] H => A (embed f))
    (actual_source_sylvester advanced F μ hμ (SourceEscapeSeedTail.actualIncrement sharp m ell))
  simp only [sub_apply,smul_apply,mul_apply_eq_comp] at hs
  simpa only [map_sub,map_smul,actual_source_L_core,compression_embed,←literal_increment_core] using hs

private theorem channel_pair (F : Index) (i : Channel F) (x y : H) :
    inner ℂ x (channel F i y) = inner ℂ (channel F i x) y := by
  cases i with
  | none =>
    change inner ℂ x (y-(supportSpan F).starProjection y) =
      inner ℂ (x-(supportSpan F).starProjection x) y
    rw [inner_sub_right,inner_sub_left,Submodule.inner_starProjection_left_eq_right]
  | some i =>
    rw [channel_some,channel_some,inner_smul_left,inner_smul_right]
    rw [inner_conj_symm x ((sourceBasis F) i : H)]
    ring

private theorem coefficient_pair (advanced : Bool) (μ a b : ℝ) :
    star (coefficient advanced μ a b) = coefficient advanced μ b a := by
  have he : star (SourceFourPoleEnergyClosed.gap μ a b) = SourceFourPoleEnergyClosed.gap μ b a := by
    simp only [SourceFourPoleEnergyClosed.gap,map_add,map_mul,map_sub,Complex.star_def,
      Complex.conj_ofReal,Complex.conj_ofNat,Complex.conj_I]
    ring
  have he' := congrArg (star : ℂ → ℂ) he
  simp only [star_star] at he'
  cases advanced
  · change star ((SourceFourPoleEnergyClosed.gap μ a b)⁻¹) = (SourceFourPoleEnergyClosed.gap μ b a)⁻¹
    rw [star_inv₀,he]
  · change star (star ((SourceFourPoleEnergyClosed.gap μ a b)⁻¹)) = star ((SourceFourPoleEnergyClosed.gap μ b a)⁻¹)
    rw [star_star,star_inv₀,←he']

private theorem increment_adjoint (sharp : Bool) (m ell : ℕ) :
    (SourceEscapeSeedTail.actualIncrement sharp m ell).adjoint = SourceEscapeSeedTail.actualIncrement (!sharp) m ell := by
  cases sharp
  · change (FullYSourceCutoffVolterra.cutoff ell-FullYSourceCutoffVolterra.cutoff m).adjoint =
      (FullYSourceCutoffVolterra.cutoff ell).adjoint-(FullYSourceCutoffVolterra.cutoff m).adjoint
    exact map_sub _ _ _
  · change ((FullYSourceCutoffVolterra.cutoff ell).adjoint-(FullYSourceCutoffVolterra.cutoff m).adjoint).adjoint =
      FullYSourceCutoffVolterra.cutoff ell-FullYSourceCutoffVolterra.cutoff m
    rw [map_sub,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.adjoint_adjoint]

/-- The exact smoothing's paired branch flips sharp and keeps the same cause. -/
theorem actual_source_core_pair (advanced sharp : Bool) (F : Index) (μ : ℝ) (m ell : ℕ)
    (f g : QuantumTest) :
    sourcePair f (sourceLCore advanced sharp F μ m ell g) =
      sourcePair (sourceLCore advanced (!sharp) F μ m ell f) g := by
  simp only [sourcePair,actual_source_L_core,actual_source_L]
  rw [inner_sum,sum_inner]
  simp only [inner_smul_right,inner_smul_left,starRingEnd_apply]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralLeg,coefficient_pair]
  rw [channel_pair,←ContinuousLinearMap.adjoint_inner_left,increment_adjoint,←channel_pair]

/-- Exact source forcing balance for the boundary price. The moving CF input current is retained. -/
theorem actual_boundary_forcing_balance (advanced sharp : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (m ell : ℕ) (f : QuantumTest) :
    2*μ*‖embed (sourceLCore advanced sharp F μ m ell f)‖^2 =
      (sourcePair (sourceLCore advanced sharp F μ m ell f) (literalIncrementAction sharp m ell f)).re +
      (if advanced then -1 else 1 : ℝ) *
        (sourcePair (sourceLCore advanced sharp F μ m ell f)
          (sourceLCore advanced sharp F μ m ell (compressionCore F f))).im := by
  have hs := congrArg (fun q : QuantumTest =>
      (sourcePair (sourceLCore advanced sharp F μ m ell f) q).re)
    (actual_source_core_sylvester advanced sharp F μ hμ m ell f)
  have hr : (sourcePair (sourceLCore advanced sharp F μ m ell f)
      (compressionCore F (sourceLCore advanced sharp F μ m ell f))).im = 0 := by
    change (inner ℂ (embed (sourceLCore advanced sharp F μ m ell f))
      (embed (compressionCore F (sourceLCore advanced sharp F μ m ell f)))).im = 0
    rw [compression_embed]
    exact (GaussGradedCompression.compression_selfAdjoint F).isSymmetric.im_inner_self_apply _
  have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed (sourceLCore advanced sharp F μ m ell f))

  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right] at hs
  cases advanced
  all_goals
    have hr' := hr
    dsimp only [sourcePair] at hr' ⊢
    rw [hn] at hs
    norm_num [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im] at hs ⊢
    linarith only [hs,hr']

end LowEnergy.ActualSylvesterCore
