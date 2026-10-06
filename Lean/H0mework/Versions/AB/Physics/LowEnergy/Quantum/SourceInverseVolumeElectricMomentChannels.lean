import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricSourceMomentBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseElectricMomentChannels
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceJointResidualEnergy
open SourceActualResolventEnergy SourceRetardedIncrement FullYSourceResolventGraphSplice
open SourceInverseElectricSourceMomentBudget SourceResolventBandLimit
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourceRead state

/-- The same finite source channels, including escape, return both nonreal half-planes. -/
theorem actual_channels (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    finiteResolvent F z x=∑ i : Channel F,((channelValue F i : ℂ)-z)⁻¹ • channel F i x := by
  classical
  let y := (supportSpan F).orthogonalProjectionOnto x
  let r := FullYSourceResolventGraphSplice.resolvent (supportAction F) z y
  have hs := congrArg (supportSpan F).subtypeL ((sourceBasis F).sum_repr r)
  simp only [map_sum,map_smul] at hs
  have hc (i : SpectralIndex F) :
      (sourceBasis F).repr r i=((channelValue F (some i) : ℂ)-z)⁻¹*(sourceBasis F).repr y i :=
    SourceFiniteResolventEnergy.coordinate_resolvent (supportAction F)
      (support_action_selfAdjoint F) z hz y i
  simp_rw [hc,mul_smul] at hs
  change (∑ i,((channelValue F (some i) : ℂ)-z)⁻¹ •
    (sourceBasis F).repr y i • ((sourceBasis F) i : H))=(r : H) at hs
  rw [resolvent_split F z hz x]
  have he : finiteResolvent F z (supportProjection F x)=(r : H) :=
    (support_resolvent F z hz y).symm
  rw [he,←hs,Fintype.sum_option]
  simp only [channelValue,channel,Complex.ofReal_zero,zero_sub,inv_neg]
  exact add_comm _ _

def mappedChannel (F : Index) (g : diagonal.domain) (A : End) (i : Channel F) : H :=
  sourceRead F g A (channel F i (g : H))

/-- The coefficient is the original reader on its own source channel, not its all-input operator norm. -/
theorem actual_mapped_channels (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (A : End) :
    embed (A (state F z hz g))=
      ∑ i : Channel F,((channelValue F i : ℂ)-z)⁻¹ • mappedChannel F g A i := by
  have hread : sourceRead F g A (finiteResolvent F z (g : H))=embed (A (state F z hz g)) := by
    unfold state
    exact source_read_resolvent F g A z hz
  rw [←hread,actual_channels F z hz]
  simp only [map_sum,map_smul,mappedChannel]

private theorem norm_gram {ι : Type*} [Fintype ι] (a : ι → ℂ) (p : ι → H) :
    ((‖∑ i,a i • p i‖^2 : ℝ) : ℂ)=∑ i,∑ j,star (a i)*a j*inner ℂ (p i) (p j) := by
  have hi (x : H) : ((‖x‖^2 : ℝ) : ℂ)=inner ℂ x x := by
    simpa only [Complex.ofReal_pow] using! (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x).symm
  rw [hi,sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) (p : ι → H) (q : κ → H) :
    ((‖∑ i,a i • p i‖^2*‖∑ j,b j • q j‖^2 : ℝ) : ℂ)=
      ∑ i,∑ j,∑ k,∑ l,(star (a i)*a j*star (b k)*b l)*
        (inner ℂ (p i) (p j)*inner ℂ (q k) (q l)) := by
  rw [Complex.ofReal_mul,norm_gram,norm_gram]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def channelGram (F : Index) (g k : diagonal.domain) (A B : End) (i j u v : Channel F) : ℂ :=
  inner ℂ (mappedChannel F k A i) (mappedChannel F k A j)*
    inner ℂ (mappedChannel F g B u) (mappedChannel F g B v)

/-- All cross-channel interference of the actual product moment is retained with its mixed causal ordering. -/
theorem actual_moment_channels (F : Index) (μ : ℝ) (hμ : 0<μ) (w : ℝ)
    (g k : diagonal.domain) (A B : End) :
    ((‖embed (A (state F (star (line μ w))
        (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne') k))‖^2*
      ‖embed (B (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2 : ℝ) : ℂ)=
      ∑ i : Channel F,∑ j : Channel F,∑ u : Channel F,∑ v : Channel F,
        (star (polePair μ (channelValue F j) (channelValue F u) w)*
          polePair μ (channelValue F i) (channelValue F v) w)*channelGram F g k A B i j u v := by
  have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
  rw [actual_mapped_channels,actual_mapped_channels]
  have hstar (i : Channel F) : ((channelValue F i : ℂ)-star (line μ w))⁻¹=
      star (pole μ (channelValue F i) w) := by
    simp only [pole,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]
  simp_rw [hstar]
  rw [pair_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [star_star,polePair,star_mul,channelGram,pole]
  ring

end LowEnergy.SourceInverseElectricMomentChannels
