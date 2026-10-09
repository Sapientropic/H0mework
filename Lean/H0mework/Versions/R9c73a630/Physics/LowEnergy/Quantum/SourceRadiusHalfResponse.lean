import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceRadiusHalfHamiltonian
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceRadiusResponseChannels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfResponse
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceRadiusHalfWindow SourceRadiusHalfHamiltonian SourceRadiusHalfKinetic SourceInverseNoetherChannelGap
open SourceJointResidualEnergy SourceScalarInverseNativeEnergy SourceResolventBandLimit FullYSourceResolventGraphSplice
open scoped InnerProductSpace

/-- Both projection-defect words belong to the same original compression. -/
def correctedCurrent (F : Index) (m ell : ℕ) : CoreEnd := radialAction m ell-
  (defectAction F*halfAction m ell-halfAction m ell*defectAction F)

theorem original_corrected_current (F : Index) (m ell : ℕ) :
    correctedCurrent F m ell=compressionCore F*halfAction m ell-halfAction m ell*compressionCore F := by
  have h := original_diagonal_current m ell
  unfold correctedCurrent defectAction
  linear_combination (norm := noncomm_ring) -h

/-- The generated local current and both defects are inserted into the actual resolvent, on its original core. -/
theorem actual_half_transport (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (halfAction m ell (state F z hz g))=
      finiteResolvent F z (embed (halfAction m ell (coreEquiv.symm g)))+
      finiteResolvent F z (embed (correctedCurrent F m ell (state F z hz g))) := by
  have hc : transportCorrection F (halfAction m ell) (state F z hz g)=
      embed (correctedCurrent F m ell (state F z hz g)) := by
    have hh : diagonalAction*halfAction m ell-halfAction m ell*diagonalAction=radialAction m ell := by
      rw [original_diagonal_current,add_sub_cancel_left]
    simp only [transportCorrection,hh,correctedCurrent,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  have h := actual_relative_transport F (halfAction m ell) z hz g
  change embed (halfAction m ell (state F z hz g))=
    finiteResolvent F z (embed (halfAction m ell (coreEquiv.symm g)))+
      finiteResolvent F z (transportCorrection F (halfAction m ell) (state F z hz g)) at h
  rw [hc] at h
  exact h

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_embed]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem pair_sub (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]

/-- The same actual Channel carrier retains escape and every unequal-value half-radius transition. -/
theorem actual_half_channel_gap (F : Index) (m ell : ℕ) (k g : diagonal.domain) (i j : Channel F) :
    sourcePair (channelTest F k i) (correctedCurrent F m ell (channelTest F g j))=
      ((channelValue F i : ℂ)-(channelValue F j : ℂ))*
        sourcePair (channelTest F k i) (halfAction m ell (channelTest F g j)) := by
  rw [original_corrected_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub]
  rw [compression_pair,actual_channel_eigen,actual_channel_eigen]
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  ring

/-- The contact curvature retains the original weight through the exact polarized IMS. -/
def curvature (m ell : ℕ) : CoreEnd := halfAction m ell*radialAction m ell-radialAction m ell*halfAction m ell

def defectCurvature (F : Index) (m ell : ℕ) : CoreEnd :=
  (2 : ℂ) • (halfAction m ell*defectAction F*halfAction m ell)-
    halfAction m ell*halfAction m ell*defectAction F-defectAction F*halfAction m ell*halfAction m ell

private theorem half_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (halfAction m ell q)=sourcePair (halfAction m ell p) q := multiply_pair _ _ _ _

private theorem scalar_radial (m ell : ℕ) :
    scalarKinetic*halfAction m ell-halfAction m ell*scalarKinetic=radialAction m ell := by
  rw [original_scalar_current,add_sub_cancel_left]

/-- Full complex polarization of the H0 double commutator; all native70 inverse-volume contacts remain. -/
theorem original_half_curvature (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (curvature m ell q)=-(sourceTime 0 : ℂ)*contactGram m ell p q := by
  have h := original_scalar_bilinear_ims m ell p q
  have he : curvature m ell=(2 : ℂ) • (halfAction m ell*scalarKinetic*halfAction m ell)-
      halfAction m ell*halfAction m ell*scalarKinetic-scalarKinetic*halfAction m ell*halfAction m ell := by
    rw [curvature,←scalar_radial]
    simp only [two_smul]
    noncomm_ring
  rw [he]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,sourcePair,map_sub,map_smul,
    inner_sub_right,inner_smul_right]
  change (2 : ℂ)*sourcePair p (halfAction m ell (scalarKinetic (halfAction m ell q)))-
    sourcePair p (halfAction m ell (halfAction m ell (scalarKinetic q)))-
    sourcePair p (scalarKinetic (halfAction m ell (halfAction m ell q)))=_
  rw [half_pair,half_pair,half_pair]
  linear_combination (2 : ℂ)*h

/-- The same oscillator price now controls the physical double commutator, with no window-norm cost. -/
theorem original_curvature_price (m ell : ℕ) (f : QuantumTest) :
    -(sourcePair f (curvature m ell f)).re ≤
      (3/(976*Real.sqrt 2*(m+1 : ℝ)))*inverseForm f := by
  rw [original_half_curvature]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,neg_mul,neg_neg]
  have h := original_kinetic_contact_price m ell f
  have hc : 3/(976*Real.sqrt 2*(m+1 : ℝ))=2*(3/(1952*Real.sqrt 2*(m+1 : ℝ))) := by
    field_simp
    norm_num
  rw [hc]
  nlinarith only [h]

/-- Exact finite-F curvature keeps its complete three-word projection defect beside the now paid source contact. -/
theorem actual_corrected_curvature (F : Index) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p ((halfAction m ell*correctedCurrent F m ell-correctedCurrent F m ell*halfAction m ell) q)=
      -(sourceTime 0 : ℂ)*contactGram m ell p q-sourcePair p (defectCurvature F m ell q) := by
  have he : halfAction m ell*correctedCurrent F m ell-correctedCurrent F m ell*halfAction m ell=
      curvature m ell-defectCurvature F m ell := by
    unfold correctedCurrent curvature defectCurvature
    simp only [two_smul]
    noncomm_ring
  rw [he,LinearMap.sub_apply,pair_sub,original_half_curvature]

/-- The complete mixed causal response retains every unequal-value radial coefficient and its actual pole pair. -/
theorem actual_half_response_channels (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (k g : diagonal.domain) :
    sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (correctedCurrent F m ell (state F z hz g))=
      ∑ i : Channel F,∑ j : Channel F,
        (((channelValue F i : ℂ)-z)⁻¹*((channelValue F j : ℂ)-z)⁻¹)*
        (((channelValue F i : ℂ)-(channelValue F j : ℂ))*
          sourcePair (channelTest F k i) (halfAction m ell (channelTest F g j))) := by
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
  change _*(_*sourcePair (channelTest F k i) (correctedCurrent F m ell (channelTest F g j)))=_
  rw [actual_half_channel_gap]
  simp only [sourcePair]
  ring

/-- Exact source energy balance of the localized moving leg; the current still contains both projection defects. -/
theorem actual_half_localized_balance (F : Index) (m ell : ℕ) (μ w : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    let f := state F (line μ w) (by simpa only [line_im] using hμ.ne') g
    μ*‖embed (halfAction m ell f)‖^2=
      -(sourcePair (halfAction m ell f) (halfAction m ell (coreEquiv.symm g))).im-
      (sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im := by
  dsimp only
  let z := line μ w
  have hz : z.im≠0 := by simpa only [z,line_im] using hμ.ne'
  let f := state F z hz g
  have hc : compressionCore F f=coreEquiv.symm g+z • f := by
    have h := actual_raised_source F z hz g 1
    simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add,
      defectAction,LinearMap.sub_apply] at h
    change diagonalAction f=coreEquiv.symm g+z • f+(diagonalAction f-compressionCore F f) at h
    linear_combination (norm := module) h
  have hroute : compressionCore F (halfAction m ell f)=
      halfAction m ell (coreEquiv.symm g)+z • halfAction m ell f+correctedCurrent F m ell f := by
    have h := LinearMap.congr_fun (original_corrected_current F m ell) f
    simp only [LinearMap.sub_apply,Module.End.mul_apply,hc,map_add,map_smul] at h
    linear_combination (norm := module) -h
  have hreal : (sourcePair (halfAction m ell f) (compressionCore F (halfAction m ell f))).im=0 := by
    have h := congrArg Complex.im (pair_conjugate (halfAction m ell f) (compressionCore F (halfAction m ell f)))
    rw [←compression_pair] at h
    simp only [Complex.conj_im] at h
    linarith
  have hnorm : inner ℂ (embed (halfAction m ell f)) (embed (halfAction m ell f))=
      ((‖embed (halfAction m ell f)‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed (halfAction m ell f))
  have h := congrArg (fun q => (sourcePair (halfAction m ell f) q).im) hroute
  rw [hreal] at h
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right] at h
  rw [hnorm] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add] at h
  have hzμ : z.im=μ := line_im μ w
  rw [hzμ] at h
  change μ*‖embed (halfAction m ell f)‖^2=_
  change μ*‖embed (halfAction m ell f)‖^2=
    -(inner ℂ (embed (halfAction m ell f)) (embed (halfAction m ell (coreEquiv.symm g)))).im-
    (inner ℂ (embed (halfAction m ell f)) (embed (correctedCurrent F m ell f))).im
  linarith only [h]

end LowEnergy.SourceRadiusHalfResponse
