import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeDivergence
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialNativeAbsorption
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceClockYukawaCubicCurrent SourceClockYukawaRadialMixedCore SourceClockYukawaRadialMixedClock
open SourceClockYukawaRadialNativeBudget SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialCoefficient
open SourceClockReflectedForm SourceRelativePowerTail SourceEscapeSeedTail
open SourceLocalizedInverseFormPayment FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction compressionCore defectAction inverseRadius finiteResolvent
  GaussGradedCompression.compression mixedState mixedForcing mixedPrice resolventCore

abbrev inputSource (g : diagonal.domain) := SourceClockYukawaRadialMixedBudget.radiusSource g

def nativeForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  nativeDivergenceWord sharp m ell (radialCore F z hz (inputSource g))
    (cutoffResponseCore sharp m ell F z hz (inputSource g))

def remainingForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  let q := state F z hz (inputSource g)
  let rS := radialCore F z hz (inputSource g)
  let rA := cutoffResponseCore sharp m ell F z hz (inputSource g)
  sourceZeroOrderWord sharp m ell rS rA q-
    bracket (defectAction F) (SourceCutoffDilationWard.literalIncrementAction sharp m ell) rS-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction) (SourceCutoffDilationWard.literalIncrementAction sharp m ell) q

/-- The actual forcing loses its native exterior derivatives as one divergence;
the full zero-order and compression words remain together. -/
theorem actual_mixed_forcing_split (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    mixedForcing sharp m ell F z hz g=nativeForce sharp m ell F z hz g+remainingForce sharp m ell F z hz g := by
  have h := actual_native_mixed_forcing sharp m ell F
    (radialCore F z hz (inputSource g)) (cutoffResponseCore sharp m ell F z hz (inputSource g))
    (state F z hz (inputSource g))
  have hr : resolventCore F z hz (coreEquiv.symm (inputSource g))=state F z hz (inputSource g) := by
    unfold resolventCore
    change state F z hz (coreEquiv (coreEquiv.symm (inputSource g)))=_
    rw [coreEquiv.apply_symm_apply]
  unfold mixedForcing
  change correctedCutoffCore sharp m ell F (resolventCore F z hz
      (SourceRadiusResponseDecay.radialCurrent F (resolventCore F z hz (coreEquiv.symm (inputSource g)))))+
    SourceRadiusResponseDecay.radialCurrent F (resolventCore F z hz
      (correctedCutoffCore sharp m ell F (resolventCore F z hz (coreEquiv.symm (inputSource g)))))-
    correctedJoinedCore sharp m ell F (resolventCore F z hz (coreEquiv.symm (inputSource g)))=_
  rw [hr]
  simp only [resolventCore]
  change correctedCutoffCore sharp m ell F (radialCore F z hz (inputSource g))+
    SourceRadiusResponseDecay.radialCurrent F (cutoffResponseCore sharp m ell F z hz (inputSource g))-
    correctedJoinedCore sharp m ell F (state F z hz (inputSource g))=_
  rw [h]
  unfold nativeForce remainingForce
  abel_nf

def coefficientEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  ∑ a : ScalarIndex,‖embed (rightNativeCoefficient sharp a m ell F z hz (inputSource g))‖^2

private theorem native_inverse (v : Ambient) : Commute (covariantMomentum v) inverseVolumeAction := by
  have h := SourceHamiltonianVolume.native_momentum_volume v
  have hVU : Commute inverseVolumeAction SourceCoframeVolume.volumeAction := by
    unfold inverseVolumeAction
    exact SourceHamiltonianVolume.real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (SourceCoframeVolume.volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem native_row_pair (a : ScalarIndex) (p f : QuantumTest) :
    sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth f))=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) f := by
  rw [GaussNativeForm.adjoint_pair,weight_inverse,LinearMap.smul_apply]
  rw [show sourcePair (covariantMomentum (scalarDirection a) p) ((-(sourceTime 0:ℂ)) • inverseVolumeAction f)=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f) by
        simp only [sourcePair,map_smul,inner_smul_right]]
  have hp : sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f)=
      sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) p)) f := multiply_pair _ _ _ _
  have hc := LinearMap.congr_fun (native_inverse (scalarDirection a)).eq p
  change covariantMomentum (scalarDirection a) (inverseVolumeAction p)=
    inverseVolumeAction (covariantMomentum (scalarDirection a) p) at hc
  rw [hp,←hc]

private theorem native_pair (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (p : QuantumTest) :
    sourcePair p (nativeForce sharp m ell F z hz g)=
      (Complex.I*(sourceTime 0:ℂ))*(∑ a : ScalarIndex,
        sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction p))
          (rightNativeCoefficient sharp a m ell F z hz (inputSource g))) := by
  unfold nativeForce nativeDivergenceWord
  simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change (-Complex.I)*(∑ a : ScalarIndex,sourcePair p
    (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth
      (rightNativeCoefficient sharp a m ell F z hz (inputSource g)))))=_
  simp_rw [native_row_pair]
  rw [←Finset.mul_sum]
  simp only [sourcePair]
  ring

private theorem gram_bound (p q : ScalarIndex → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤
      (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ScalarIndex) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem native_pair_square (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (p : QuantumTest) :
    ‖sourcePair p (nativeForce sharp m ell F z hz g)‖^2 ≤
      (sourceTime 0)^2*scalarForm (inverseVolumeAction p)*coefficientEnergy sharp m ell F z hz g := by
  rw [native_pair,norm_mul,mul_pow]
  have hn : ‖Complex.I*(sourceTime 0:ℂ)‖^2=(sourceTime 0)^2 := by
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hn]
  have h := gram_bound (fun a => covariantMomentum (scalarDirection a) (inverseVolumeAction p))
    (fun a => rightNativeCoefficient sharp a m ell F z hz (inputSource g))
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by
    simp only [scalarForm,coefficientEnergy,mul_assoc])

private theorem young_of_square (a p q η : ℝ) (_ha : 0 ≤ a) (hp : 0 ≤ p) (hq : 0 ≤ q) (hη : 0 < η)
    (hs : a^2≤2*p*q) : a≤η*p+q/(2*η) := by
  have hpos : 0 ≤ η*p+q/(2*η) := by positivity
  have he : 4*(η*p)*(q/(2*η))=2*p*q := by field_simp;ring
  nlinarith only [hs,sq_nonneg (η*p-q/(2*η)),he,hpos]

/-- The original positive scalar slot of the same mixed response pays its
native divergence; no graph estimate or external momentum price is supplied. -/
theorem actual_native_divergence_price (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    ‖sourcePair (mixedState sharp m ell F z hz g) (nativeForce sharp m ell F z hz g)‖ ≤
      η*mixedPrice sharp m ell F z hz g+coefficientEnergy sharp m ell F z hz g/(2*η) := by
  let qM := mixedState sharp m ell F z hz g
  have hg : 0 ≤ coefficientEnergy sharp m ell F z hz g := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : 0 ≤ scalarForm (inverseVolumeAction qM) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := (actual_mixed_positive_payment sharp m ell F z hz g).2.1
  have h0 : 0 ≤ mixedPrice sharp m ell F z hz g :=
    (mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/2) hS).trans hp
  apply young_of_square _ _ _ η (norm_nonneg _) h0 hg hη
  have hn := native_pair_square sharp m ell F z hz g qM
  have he := mul_le_mul_of_nonneg_right hp hg
  nlinarith only [hn,he]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=finiteResolvent F z
      (SourceClockYukawaRadialMixedGamma.radialCurrent F (finiteResolvent F z (g:H))) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core,state_embed]
  simp only [SourceClockYukawaRadialMixedGamma.radialCurrent,mul_apply_eq_comp,sub_apply,map_sub]

private theorem cutoff_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    embed (cutoffResponseCore sharp m ell F z hz g)=finiteResolvent F z
      (SourceClockYukawaRadialMixedGamma.cutoffCurrent sharp m ell F (finiteResolvent F z (g:H))) := by
  rw [cutoffResponseCore,state_embed]
  change finiteResolvent F z (embed (correctedCutoffCore sharp m ell F (state F z hz g)))=_
  rw [←actual_cutoff_current_source,state_embed]

private theorem derivative_embed (a : ScalarIndex) (f : QuantumTest) :
    embed (inverseDerivativeCore a f)=inverseDerivative a (embed f) := by
  simp only [inverseDerivative,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    inverse_core,original_direction_core]

private theorem coefficient_energy_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (coefficientEnergy sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g)) := by
  have he (w : ℝ) (a : ScalarIndex) :
      embed (rightNativeCoefficient sharp a m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') (inputSource g))=
      SourceLocalizedInverseFormPayment.boundedCoefficient sharp a m ell (finiteResolvent F (line μ w)
        (SourceClockYukawaRadialMixedGamma.radialCurrent F (finiteResolvent F (line μ w) (inputSource g:H))))+
      inverseDerivative a (finiteResolvent F (line μ w)
        (SourceClockYukawaRadialMixedGamma.cutoffCurrent sharp m ell F
          (finiteResolvent F (line μ w) (inputSource g:H)))) := by
    rw [rightNativeCoefficient,map_add,←SourceLocalizedInverseFormPayment.original_bounded_coefficient_core,
      radial_embed,derivative_embed,cutoff_embed]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc : Continuous (fun w : ℝ => coefficientEnergy sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g) := by
    simp only [coefficientEnergy,he]
    apply continuous_finsetSum
    intro a _
    exact ((((SourceLocalizedInverseFormPayment.boundedCoefficient sharp a m ell).continuous.comp
      (hr.clm_apply ((SourceClockYukawaRadialMixedGamma.radialCurrent F).continuous.comp
        (hr.clm_apply continuous_const)))).add ((inverseDerivative a).continuous.comp
      (hr.clm_apply ((SourceClockYukawaRadialMixedGamma.cutoffCurrent sharp m ell F).continuous.comp
        (hr.clm_apply continuous_const))))).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

/-- The entire zero-order/full-defect source word remains signed after the
native scalar price is absorbed at the same mixed response. -/
def remainingPrice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) : ℝ :=
  η*mixedPrice sharp m ell F z hz g-
    (sourcePair (mixedState sharp m ell F z hz g) (remainingForce sharp m ell F z hz g)).im

def remainingBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (remainingPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)

def mixedNormEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (μ*‖embed (mixedState sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)‖^2)

private theorem mu_remaining_point (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    z.im*‖embed (mixedState sharp m ell F z hz g)‖^2 ≤
      remainingPrice sharp m ell F z hz g η+coefficientEnergy sharp m ell F z hz g/(2*η) := by
  have h := actual_mixed_mu_ward sharp m ell F z hz g
  rw [actual_mixed_forcing_split] at h
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  have hp := actual_native_divergence_price sharp m ell F z hz g η hη
  have hi := (neg_le_abs (sourcePair (mixedState sharp m ell F z hz g)
    (nativeForce sharp m ell F z hz g)).im).trans (Complex.abs_im_le_norm _)
  unfold remainingPrice
  change z.im*‖embed (mixedState sharp m ell F z hz g)‖^2=
    -((sourcePair (mixedState sharp m ell F z hz g) (nativeForce sharp m ell F z hz g)).im+
      (sourcePair (mixedState sharp m ell F z hz g) (remainingForce sharp m ell F z hz g)).im) at h
  linarith only [h,hp,hi]

private theorem remaining_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        mixedNormEnergy sharp m ell F μ hμ g ≤ ENNReal.ofReal ε+remainingBudget sharp m ell F μ hμ g η := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_right_native_coefficient_tail sharp μ hμ (inputSource g) (2*η*ε) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  let G (w : ℝ) := ENNReal.ofReal (coefficientEnergy sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)
  let Q (w : ℝ) := ENNReal.ofReal (remainingPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)
  have hG : Measurable (fun w => ENNReal.ofReal (1/(2*η))*G w) :=
    (coefficient_energy_measurable sharp m ell F μ hμ g).const_mul _
  have hb : (∫⁻ w : ℝ,G w) ≤ ENNReal.ofReal (2*η*ε) := hF
  have he : ENNReal.ofReal (1/(2*η))*ENNReal.ofReal (2*η*ε)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc
    _ ≤ ∫⁻ w : ℝ,Q w+ENNReal.ofReal (1/(2*η))*G w := by
      apply lintegral_mono
      intro w
      have hp := mu_remaining_point sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η hη
      simp only [line_im] at hp
      change ENNReal.ofReal _ ≤ _
      calc
        _ ≤ ENNReal.ofReal (remainingPrice sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g η+
            coefficientEnergy sharp m ell F (line μ w)
              (by simpa only [line_im] using hμ.ne') g/(2*η)) := ENNReal.ofReal_le_ofReal hp
        _ ≤ Q w+ENNReal.ofReal (1/(2*η))*G w := by
          have hadd := ENNReal.ofReal_add_le (p := remainingPrice sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g η)
            (q := coefficientEnergy sharp m ell F (line μ w)
              (by simpa only [line_im] using hμ.ne') g/(2*η))
          simpa only [Q,G,div_eq_inv_mul,ENNReal.ofReal_mul (show 0 ≤ (2*η)⁻¹ by positivity),one_div,ENNReal.ofReal_one,mul_one] using hadd
    _=(∫⁻ w : ℝ,Q w)+ENNReal.ofReal (1/(2*η))*(∫⁻ w : ℝ,G w) := by
      rw [lintegral_add_right _ hG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (∫⁻ w : ℝ,Q w)+ENNReal.ofReal ε := add_le_add (le_refl _) ((mul_le_mul (le_refl _) hb zero_le zero_le).trans_eq he)
    _=_ := by rw [add_comm];rfl

/-- A single original-source cutoff pays the complete native divergence for
both Yukawa branches; the remaining whole source word is preserved inside one positive part. -/
theorem actual_mixed_mu_remaining_budget (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        mixedNormEnergy sharp m ell F μ hμ g ≤ ENNReal.ofReal ε+remainingBudget sharp m ell F μ hμ g η := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := remaining_common_tail false μ hμ g η hη ε hε
  obtain ⟨N₁,h₁⟩ := remaining_common_tail true μ hμ g η hη ε hε
  refine ⟨max N₀ N₁,fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml,
    h₁ m ((le_max_right _ _).trans hm) ell hml] with F hf ht sharp
  cases sharp
  · exact hf
  · exact ht

end LowEnergy.SourceClockYukawaRadialNativeAbsorption
