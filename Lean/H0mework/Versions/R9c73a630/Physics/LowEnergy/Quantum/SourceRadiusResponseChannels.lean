import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceRadiusResponseDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceRadiusResponseChannels
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussDiagonalHistory GaussUnitaryHistory
open GaussRadialDomain SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceRadiusResponseDecay SourceInverseNoetherChannelGap SourceJointResidualEnergy
open FullYSourceResolventGraphSplice
open scoped InnerProductSpace

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The whole-H response is exactly the original radial action minus both projection-defect words. -/
theorem actual_response_source (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    response F z (g : H)=finiteResolvent F z (embed (radialCurrent F (state F z hz g))) := by
  rw [original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core]
  have hs : embed (state F z hz g)=finiteResolvent F z (g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [hs]
  simp only [response,sub_apply,mul_apply_eq_comp,map_sub]

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_embed]
  exact (GaussGradedCompression.compression_pair F _ _).symm

private theorem pair_sub (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]

/-- Original eigenvalue differences multiply every corrected radial transition, including escape. -/
theorem actual_radial_channel_gap (F : Index) (k g : diagonal.domain) (i j : Channel F) :
    sourcePair (channelTest F k i) (radialCurrent F (channelTest F g j))=
      ((channelValue F i : ℂ)-(channelValue F j : ℂ))*
        sourcePair (channelTest F k i) (inverseAction (channelTest F g j)) := by
  rw [original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub]
  rw [compression_pair,actual_channel_eigen,actual_channel_eigen]
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  ring

theorem actual_equal_value_radial_zero (F : Index) (k g : diagonal.domain) (i j : Channel F)
    (h : channelValue F i=channelValue F j) :
    sourcePair (channelTest F k i) (radialCurrent F (channelTest F g j))=0 := by
  rw [actual_radial_channel_gap,h,sub_self,zero_mul]

/-- The complete mixed causal response retains every unequal-value radial coefficient and its actual pole pair. -/
theorem actual_radial_response_channels (F : Index) (z : ℂ) (hz : z.im≠0) (k g : diagonal.domain) :
    sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (radialCurrent F (state F z hz g))=
      ∑ i : Channel F,∑ j : Channel F,
        (((channelValue F i : ℂ)-z)⁻¹*((channelValue F j : ℂ)-z)⁻¹)*
        (((channelValue F i : ℂ)-(channelValue F j : ℂ))*
          sourcePair (channelTest F k i) (inverseAction (channelTest F g j))) := by
  rw [actual_state_channels,actual_state_channels]
  simp only [map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  have hs (i : Channel F) : star (((channelValue F i : ℂ)-star z)⁻¹)=((channelValue F i : ℂ)-z)⁻¹ := by
    simp
  simp only [starRingEnd_apply,hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _*(_*sourcePair (channelTest F k i) (radialCurrent F (channelTest F g j)))=_
  rw [actual_radial_channel_gap]
  simp only [sourcePair]
  ring

end LowEnergy.SourceRadiusResponseChannels
