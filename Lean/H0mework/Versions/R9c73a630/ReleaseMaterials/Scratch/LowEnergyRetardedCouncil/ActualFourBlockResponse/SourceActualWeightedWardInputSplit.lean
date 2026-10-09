import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWeightedWardFrequencyReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualInverseCurrentCoframeReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualWeightedWardInputSplit
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk SourcePhysicalKineticSquare
open ActualInverseCurrentCoframeReturn
open SourceScalarInverseBulk ActualMixedCovarianceTail ActualMixedWindowGram ActualMixedWardTail
open ActualMixedWardPolarization ActualMixedWardMomentTail ActualMixedFrequencyJet
open ActualVectorJointCost SourceResolventBandLimit FullYSourceResolventGraphSplice SourceNativeCutoffContact
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore diagonalAction

elab "paid_weighted_inverse%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard 0) "LowEnergy") "ActualMixedResolventWard"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing actual source inverse proof"
  mkConstWithFreshMVarLevels name

private theorem inverse_pair (F:Index)(z:ℂ)(hz:z.im≠0):
    resolventCore F z hz*(compressionCore F-z • (1:End))=1 ∧
      (compressionCore F-z • (1:End))*resolventCore F z hz=1 :=
  (paid_weighted_inverse% actual_inverse) F z hz

/-- The source weight returns through a fixed input and this one full coframe word. -/
def coframeFlux (F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F z hz*(compressionCore F*inverseVolumeAction-
    inverseVolumeAction*compressionCore F)*resolventCore F z hz

theorem actual_inverse_input (F:Index)(z:ℂ)(hz:z.im≠0):
    inverseVolumeAction*resolventCore F z hz=
      resolventCore F z hz*inverseVolumeAction+coframeFlux F z hz := by
  have hi:=inverse_pair F z hz
  have h:=(paid_weighted_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) inverseVolumeAction hi.1 hi.2
  simp only [(paid_weighted_inverse% comm_spectral)] at h
  change inverseVolumeAction*resolventCore F z hz-resolventCore F z hz*inverseVolumeAction=
    -resolventCore F z hz*(inverseVolumeAction*compressionCore F-compressionCore F*inverseVolumeAction)*resolventCore F z hz at h
  unfold coframeFlux
  linear_combination (norm:=noncomm_ring) h

/-- Both actual occurrences are retained when CF is read at H0. -/
theorem actual_coframe_flux_source (F:Index)(z:ℂ)(hz:z.im≠0):
    coframeFlux F z hz=
      resolventCore F z hz*(diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)*resolventCore F z hz-
      resolventCore F z hz*(defectAction F*inverseVolumeAction-inverseVolumeAction*defectAction F)*resolventCore F z hz := by
  have hc:compressionCore F=diagonalAction-defectAction F := by unfold defectAction;abel
  unfold coframeFlux
  rw [hc]
  noncomm_ring

private theorem inverse_theta (m ell:ℕ):Commute inverseVolumeAction (thetaAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourcePhysicalKineticSquare.reciprocalVolume z:ℂ)
    (SourceNativeCutoffContact.theta m ell z:ℂ) (f z)

/-- The weighted window pairing has a fixed Ug leg plus the actual same-CF flux. -/
theorem actual_weighted_window_input (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    sourcePair (coreWindow m ell F z hz g) (inverseVolumeAction (coreWindow m ell F z hz h))=
      sourcePair (coreWindow m ell F z hz g) (coreWindow m ell F z hz (inverseVolumeAction h))+
      sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (coframeFlux F z hz h)) := by
  have he:=LinearMap.congr_fun (actual_inverse_input F z hz) h
  have hc:=LinearMap.congr_fun (inverse_theta m ell).eq (resolventCore F z hz h)
  change inverseVolumeAction (thetaAction m ell (resolventCore F z hz h))=
    thetaAction m ell (inverseVolumeAction (resolventCore F z hz h)) at hc
  change inverseVolumeAction (resolventCore F z hz h)=
    resolventCore F z hz (inverseVolumeAction h)+coframeFlux F z hz h at he
  simp only [coreWindow,Module.End.mul_apply]
  rw [hc,he]
  simp only [map_add,sourcePair,inner_add_right]

private theorem star_nonreal (z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

def weightedCovariance (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*inverseVolumeAction*
    thetaAction m ell*resolventCore F z hz

/-- The actual covariance keeps the whole unbounded weight in one coframe correction. -/
theorem actual_weighted_covariance_input (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    weightedCovariance m ell F z hz=coreCovariance m ell F z hz*inverseVolumeAction+
      resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*thetaAction m ell*coframeFlux F z hz := by
  unfold weightedCovariance coreCovariance
  let R:=resolventCore F z hz
  let S:=resolventCore F (star z) (star_nonreal z hz)
  let T:=thetaAction m ell
  change S*T*inverseVolumeAction*T*R=S*T*T*R*inverseVolumeAction+S*T*T*coframeFlux F z hz
  calc
    _=S*T*(inverseVolumeAction*T)*R := by noncomm_ring
    _=S*T*(T*inverseVolumeAction)*R := by rw [(inverse_theta m ell).eq]
    _=S*T*T*(inverseVolumeAction*R) := by noncomm_ring
    _=_ := by rw [actual_inverse_input];noncomm_ring

private theorem inverse_second_zero:secondJet inverseVolumeAction=0 := by
  change (deltaPhi inverseVolumeAction-deltaGauge inverseVolumeAction)-
    deltaGauge (deltaPhi inverseVolumeAction-deltaGauge inverseVolumeAction)=0
  have hp:deltaPhi inverseVolumeAction=(0:End) := SourceScalarInverseBulk.inverse_phi
  have hg:deltaGauge inverseVolumeAction=(0:End) := SourceScalarInverseBulk.inverse_gauge
  have hz:deltaGauge (0:End)=(0:End) := deltaGauge.map_zero
  rw [hp,hg]
  simp only [sub_self,hz]

/-- Phi/Gauge leave U fixed, so all extra mixed source terms stay in the same
coframe correction. No weighted-family tail is assumed. -/
theorem actual_weighted_second_covariance_input (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    secondJet (weightedCovariance m ell F z hz)=secondJet (coreCovariance m ell F z hz)*inverseVolumeAction+
      secondJet (resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*thetaAction m ell*coframeFlux F z hz) := by
  rw [actual_weighted_covariance_input,map_add,actual_second_product,
    inverse_second_zero,inverse_phi,inverse_gauge,sub_self]
  simp only [mul_zero,sub_zero,add_zero]

/-- The native middle current has no mixed source jet. The surrounding inverse
jets and the one complete own-defect word remain in their original order. -/
theorem actual_weighted_mixed_source_return (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    let R:=resolventCore F z hz
    let C:=coreCovariance m ell F z hz
    secondJet (weightedCovariance m ell F z hz)=
      secondJet C*inverseVolumeAction+
      (secondJet C*hamiltonianCurrent*R+C*hamiltonianCurrent*secondJet R-
        deltaGauge C*hamiltonianCurrent*(deltaPhi R-deltaGauge R)-
        (deltaPhi C-deltaGauge C)*hamiltonianCurrent*deltaGauge R-
        secondJet (C*ownCurrent F*R)) := by
  dsimp only
  rw [actual_weighted_second_covariance_input]
  have he:resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*thetaAction m ell*coframeFlux F z hz=
      coreCovariance m ell F z hz*compressedCurrent F*resolventCore F z hz := by
    unfold coframeFlux coreCovariance compressedCurrent
    noncomm_ring
  rw [he,actual_mixed_inverse_current_product]

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem four_complex_price (a b c d:ℂ):
    ‖(a-b-Complex.I*(c-d))/4‖≤(‖a‖+‖b‖+‖c‖+‖d‖)/4 := by
  rw [norm_div]
  have h:=norm_sub_le (a-b) (Complex.I*(c-d))
  have h0:=norm_sub_le a b
  have h1:=norm_sub_le c d
  simp only [norm_mul,Complex.norm_I,one_mul] at h
  norm_num only [Complex.norm_ofNat]
  nlinarith only [h,h0,h1]

/-- Fixed original input pairs, including h=Ug, consume the paid signed moment
without selecting frequency-dependent source vectors. -/
theorem actual_polarized_frequency_moment_tail (μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        let f:=fun w:ℝ=>causalFrequency advanced μ w*
          wardPair m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g h
        Integrable f ∧ ‖∫w:ℝ,f w‖≤ε := by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_complex_frequency_moment_tail μ hμ (g+h) ε hε
  obtain ⟨N1,h1⟩:=actual_complex_frequency_moment_tail μ hμ (g-h) ε hε
  obtain ⟨N2,h2⟩:=actual_complex_frequency_moment_tail μ hμ (g+Complex.I • h) ε hε
  obtain ⟨N3,h3⟩:=actual_complex_frequency_moment_tail μ hμ (g-Complex.I • h) ε hε
  refine ⟨max (max N0 N1) (max N2 N3),fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml,
    h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hF0 hF1 hF2 hF3
  intro advanced
  obtain ⟨hi0,hp0⟩:=hF0 advanced
  obtain ⟨hi1,hp1⟩:=hF1 advanced
  obtain ⟨hi2,hp2⟩:=hF2 advanced
  obtain ⟨hi3,hp3⟩:=hF3 advanced
  dsimp only at hi0 hp0 hi1 hp1 hi2 hp2 hi3 hp3 ⊢
  let q:=fun s:QuantumTest=>fun w:ℝ=>causalFrequency advanced μ w*
    (wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) s:ℂ)
  have he:(fun w:ℝ=>causalFrequency advanced μ w*
      wardPair m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g h)=
      fun w:ℝ=>(q (g+h) w-q (g-h) w-Complex.I*(q (g+Complex.I • h) w-q (g-Complex.I • h) w))/4 := by
    funext w
    rw [actual_pair_polarization]
    dsimp only [q]
    ring
  rw [he]
  have hi01:Integrable (fun w:ℝ=>q (g+h) w-q (g-h) w) := hi0.sub hi1
  have hi23:Integrable (fun w:ℝ=>q (g+Complex.I • h) w-q (g-Complex.I • h) w) := hi2.sub hi3
  have hiI:Integrable (fun w:ℝ=>Complex.I*(q (g+Complex.I • h) w-q (g-Complex.I • h) w)) := hi23.const_mul Complex.I
  refine ⟨(hi01.sub hiI).div_const 4,?_⟩
  rw [integral_div,integral_sub hi01 hiI,integral_const_mul,
    integral_sub hi0 hi1,integral_sub hi2 hi3]
  have hp:=four_complex_price (∫w:ℝ,q (g+h) w) (∫w:ℝ,q (g-h) w)
    (∫w:ℝ,q (g+Complex.I • h) w) (∫w:ℝ,q (g-Complex.I • h) w)
  exact hp.trans (by dsimp only [q];linarith only [hp0,hp1,hp2,hp3])

end LowEnergy.ActualWeightedWardInputSplit
