import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseCompressionWard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeFrequencyWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceInverseNoetherChannelGap
open SourceJointResidualEnergy SourceInverseElectricMomentChannels SourceScalarDoubleCurrent ReverseNativeClock
open scoped Topology
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed diagonalAction compressionCore resolventCore reverseNativeClock reverseScaleForce
  coreEquiv state channelTest

theorem reverse_frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(q:ℝ):
    (actualFrequency advanced μ q).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
theorem actual_physical_frequency_derivative(advanced:Bool)(μ q:ℝ):
    HasDerivAt (actualFrequency advanced μ) 1 q:=by
  cases advanced
  · simpa only [actualFrequency,Bool.false_eq_true,ite_false,line,Complex.ofReal_one,id_eq] using!
      ((hasDerivAt_id q).ofReal_comp.add_const ((μ:ℂ)*Complex.I))
  · have h:=((hasDerivAt_id q).ofReal_comp.sub_const ((μ:ℂ)*Complex.I))
    convert! h using 1
    funext r
    simp only [actualFrequency,ite_true,line,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg]
    rfl
private theorem pole_nonzero(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    (a:ℂ)-actualFrequency advanced μ q≠0:=by
  intro h
  apply reverse_frequency_nonreal advanced μ hμ q
  rw [←sub_eq_zero.mp h]
  rfl
theorem actual_physical_pole_derivative(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    HasDerivAt (fun r:ℝ=>((a:ℂ)-actualFrequency advanced μ r)⁻¹)
      ((((a:ℂ)-actualFrequency advanced μ q)⁻¹)^2) q:=by
  have h:=((actual_physical_frequency_derivative advanced μ q).const_sub (a:ℂ)).inv
    (pole_nonzero advanced μ hμ a q)
  convert! h using 1
  simp only [neg_neg,div_eq_mul_inv,one_mul,inv_pow]

private theorem core_channels(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    resolventCore F z hz f=∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • channelTest F (coreEquiv f) j:=by
  have h:=actual_state_channels F z hz (coreEquiv f)
  simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk] using h
private theorem resolvent_channel(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest)(j:Channel F):
    resolventCore F z hz (channelTest F (coreEquiv f) j)=
      ((channelValue F j:ℂ)-z)⁻¹ • channelTest F (coreEquiv f) j:=by
  let c:=channelTest F (coreEquiv f) j
  have he:(compressionCore F-z • (1:End)) c=((channelValue F j:ℂ)-z) • c:=by
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,sub_smul,c,actual_channel_eigen]
  have hi:=LinearMap.congr_fun (actual_original_cf_inverses F z hz).2 c
  change resolventCore F z hz ((compressionCore F-z • (1:End)) c)=c at hi
  rw [he,map_smul] at hi
  have hn:(channelValue F j:ℂ)-z≠0:=by
    intro h
    apply hz
    rw [←sub_eq_zero.mp h]
    rfl
  have h:=congrArg (fun v:QuantumTest=>((channelValue F j:ℂ)-z)⁻¹ • v) hi
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul,c] using h
private theorem square_channels(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    resolventCore F z hz (resolventCore F z hz f)=
      ∑j:Channel F,(((channelValue F j:ℂ)-z)⁻¹)^2 • channelTest F (coreEquiv f) j:=by
  rw [core_channels F z hz f]
  simp only [map_sum,map_smul,resolvent_channel,smul_smul,pow_two]

/-- Every fixed source word inherits the physical-frequency derivative from the original finite and escape channels; no continuity of an arbitrary unbounded operator is assumed. -/
theorem actual_physical_resolvent_derivative(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(L:End)(f:QuantumTest)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (L (resolventCore F (actualFrequency advanced μ r)
      (reverse_frequency_nonreal advanced μ hμ r) f)))
      (embed (L (resolventCore F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q)
        (resolventCore F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) f)))) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Channel F))) (fun j _=>
    (actual_physical_pole_derivative advanced μ hμ (channelValue F j) q).smul_const (embed (L (channelTest F (coreEquiv f) j))))
  rw [square_channels F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) f]
  simpa only [core_channels,map_sum,map_smul,Finset.sum_apply] using! h

/-- Both causes have dz/domega=1. Thus the full 18H0 scale term is exactly a physical-frequency derivative of z times the actual response. -/
theorem actual_shifted_resolvent_derivative(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(L:End)(f:QuantumTest)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (L (actualFrequency advanced μ r • resolventCore F (actualFrequency advanced μ r)
      (reverse_frequency_nonreal advanced μ hμ r) f)))
      (embed (L (resolventCore F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) f+
        actualFrequency advanced μ q • resolventCore F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q)
          (resolventCore F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) f)))) q:=by
  have h:=(actual_physical_frequency_derivative advanced μ q).smul
    (actual_physical_resolvent_derivative F advanced μ hμ L f q)
  convert! h using 1
  · funext r
    simp only [map_smul]
    rfl
  · simp only [map_smul,map_add,one_smul]
    exact add_comm _ _
end LowEnergy.ReverseNativeFrequencyWard
