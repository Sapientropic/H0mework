import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarClockGainPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiRScalarAbsorption
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarInverseNativeEnergy SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarVirialBulk
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusNormalizedFluxBudget SourceClockPhiRadiusSourceCurrent
open SourceClockRadiusAffineCutoff SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceClockPhiNativeMatchedSource SourceCoframeCovariantAction NativePointReturn
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext FinitePhysicalSource MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev n : ℝ := sourceTime 0
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev K := correctedCompleteCore
private abbrev B : End := scalarBulkComplete
attribute [local irreducible] sourcePair embed normalizedState normalizedForcing diagonalAction correctedCompleteCore updatedForcing
  coframeForcing coframeCompleted completeCurrent nativeComplement matchedTester combinedConjugate
private theorem pair_add_l (f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c:ℂ) (f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r (c:ℂ) (f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem scalar_self (f:QuantumTest):sourcePair f (B f)=((scalarEnergy f:ℝ):ℂ) := by
  have hr:=original_scalar_energy f
  have hp:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B f))
  rw [←original_scalar_pair] at hp
  simp only [Complex.conj_im] at hp
  apply Complex.ext
  · exact hr
  · simp only [Complex.ofReal_im];linarith only [hp]
private theorem scalar_ward (w f:QuantumTest)(z:ℂ)(he:diagonalAction w=f+z • w):
    z.im*scalarEnergy w=(sourcePair f (B w)).im-
      (sourcePair w ((diagonalAction*B-B*diagonalAction) w)).im/2 := by
  have hp:sourcePair w ((diagonalAction*B-B*diagonalAction) w)=
      sourcePair (diagonalAction w) (B w)-sourcePair (B w) (diagonalAction w) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,original_scalar_pair]
  have hbself:sourcePair (B w) w=((scalarEnergy w:ℝ):ℂ) :=
    (original_scalar_pair w w).symm.trans (scalar_self w)
  rw [he,pair_add_l,pair_smul_l,pair_add_r,pair_smul_r,scalar_self,hbself] at hp
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  have hi:=congrArg Complex.im hp
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,mul_zero,zero_add] at hi
  linarith only [hi,hc]

private theorem n_pos : 0 < n := by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_pos (half : Bool) : 0 < sourceNoetherFrequency half := by
  linarith [actual_source_noether_gap half,n_pos]
private theorem frequency_nonreal (half advanced : Bool) (x : ℝ) :
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using (frequency_pos half).ne'
private theorem norm_cost_nonnegative (half : Bool) : 0  ≤  scalarNoetherNormCost half := by
  unfold scalarNoetherNormCost
  have hn:=n_pos
  have hk:=(actual_scalar_noether_fraction half).1
  positivity

def scalarClockWindow (half : Bool) : ℝ := 61*n/(6*(scalarNoetherNormCost half+1))
theorem actual_scalar_clock_window_positive (half : Bool) : 0 < scalarClockWindow half := by
  unfold scalarClockWindow
  have hn:=n_pos
  have hc:=norm_cost_nonnegative half
  positivity
private theorem window_payment (half : Bool) (s : ℝ) (hs:0<s) (ht:s ≤ scalarClockWindow half) :
    18*s*scalarNoetherNormCost half ≤ 183*n := by
  have hc:=norm_cost_nonnegative half
  have hd:0<6*(scalarNoetherNormCost half+1):=by positivity
  have h: s*(6*(scalarNoetherNormCost half+1)) ≤ 61*n := (le_div_iff₀ hd).mp ht
  nlinarith only [h,hs,hc]

/-- The full updated forcing and full geometric scalar current of the same corrected source. -/
def correctedScalarNoetherPrice (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let u:=K s hs ξ η (normalizedState m ell F z hz g)
  (if advanced then (-1:ℝ) else 1)*
    ((sourcePair (updatedForcing s hs (ξ,η) m ell F z hz g) (B u)).im-
      (sourcePair u (geometricScalarCurrent u)).im/2)

def correctedScalarNoetherGap (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let u:=K s hs ξ η (normalizedState m ell F z hz g)
  scalarNativePrice u-scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
    10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u

private theorem corrected_scalar_ward (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) x
    let hz:=frequency_nonreal half advanced x
    let u:=K s hs ξ η (normalizedState m ell F z hz g)
    (sourceNoetherFrequency half-2*n)*scalarEnergy u ≤
      correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+n^2*‖vacuum‖^2*‖embed u‖^2:=by
  dsimp only
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let u:=K s hs ξ η (normalizedState m ell F z hz g)
  have h:=scalar_ward u (updatedForcing s hs (ξ,η) m ell F z hz g) z
    (actual_corrected_full_forcing s hs (ξ,η) m ell F z hz g)
  rw [original_scalar_current_geometric] at h
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_im] at h
  have hb:=original_scalar_oscillator_bound u
  change |(sourcePair u (scalarCurrentComplete u)).im/2| ≤
    2*n*scalarEnergy u+n^2*‖vacuum‖^2*‖embed u‖^2 at hb
  change (sourceNoetherFrequency half-2*n)*scalarEnergy u ≤
    (if advanced then (-1:ℝ) else 1)*
    ((sourcePair (updatedForcing s hs (ξ,η) m ell F z hz g) (B u)).im-
      (sourcePair u (geometricScalarCurrent u)).im/2)+n^2*‖vacuum‖^2*‖embed u‖^2
  cases advanced
  · have hzi:z.im=sourceNoetherFrequency half:=line_im _ _
    rw [hzi] at h
    simp only [Bool.false_eq_true,ite_false,one_mul]
    have hlo:=neg_le_abs ((sourcePair u (scalarCurrentComplete u)).im/2)
    linarith only [h,hb,hlo]
  · have hzi:z.im= -sourceNoetherFrequency half:=by
      simp only [z,actualFrequency,ite_true,Complex.star_def,Complex.conj_im,line_im]
    rw [hzi] at h
    simp only [ite_true,neg_one_mul]
    have hhi:=le_abs_self ((sourcePair u (scalarCurrentComplete u)).im/2)
    linarith only [h,hb,hhi]

/-- The finite physical clock update pays its real gain from the same source's scalar squares.
The resulting norm price is on the original normalized state, with no clock or noise dependence. -/
theorem actual_corrected_scalar_noether_point_payment (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (ht:s ≤ scalarClockWindow half)(m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):
    correctedScalarNoetherGap s hs ξ η half advanced m ell F x g ≤
      scalarNoetherNormCost half*‖embed (normalizedState m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)‖^2:=by
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  let u:=K s hs ξ η w
  have hW:=corrected_scalar_ward s hs ξ η half advanced m ell F x g
  change (sourceNoetherFrequency half-2*n)*scalarEnergy u ≤
    correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+n^2*‖vacuum‖^2*‖embed u‖^2 at hW
  have hM:=mul_le_mul_of_nonneg_left hW (actual_scalar_noether_fraction half).1.le
  have hk:scalarNoetherFactor half*(sourceNoetherFrequency half-2*n)=5:=by
    unfold scalarNoetherFactor
    exact div_mul_cancel₀ _ (ne_of_gt (lt_trans (by norm_num) (actual_source_noether_gap half)))
  rw [←mul_assoc,hk] at hM
  have hS:=actual_scalar_native_joint_square u
  have hG:=actual_corrected_scalar_square_payment (scalarNoetherNormCost half)
    (norm_cost_nonnegative half) s hs (window_payment half s hs ht) ξ η w
  dsimp only at hG
  change scalarNativePrice u-scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
    10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u ≤ scalarNoetherNormCost half*‖embed w‖^2
  change scalarNoetherNormCost half*‖embed u‖^2-13*n*inverseNativeEnergy u-6*n*scalarPaymentSquare u ≤
    scalarNoetherNormCost half*‖embed w‖^2-10*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u at hG
  unfold scalarNoetherNormCost at hG ⊢
  nlinarith only [hM,hS,hG]

private abbrev S : End :=SourceClockPhiRadiusSourceCurrent.phiInverseAction
private abbrev r : End :=SourceClockPhiRadiusSourceCurrent.phiRadiusAction
private abbrev T (m ell : ℕ) : End :=phiThetaAction m ell
private theorem normalized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g):=by
  let Q : End := (1:End)-S
  have hQ(f:QuantumTest):S (Q f)=Q (S f):=by
    change S (f-S f)=S f-S (S f)
    rw [map_sub]
  have hp(k:ℕ)(f:QuantumTest):S ((Q^k) f)=(Q^k) (S f):=by
    induction k with
    | zero => simp only [pow_zero,Module.End.one_apply]
    | succ k ih =>
      rw [pow_succ']
      change S (Q ((Q^k) f))=Q ((Q^k) (S f))
      rw [hQ,ih]
  have hc : Commute S (T m ell) := by
    change S*(Q^(m+1)-Q^(ell+1))=(Q^(m+1)-Q^(ell+1))*S
    apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,hp]
  have hi(f:QuantumTest):S (r f)=f:=by
    apply DFunLike.ext
    intro q
    change (phiReciprocal q:ℂ) • ((phiRadius q:ℂ) • f q)=f q
    rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have he(f:QuantumTest):S (T m ell f)=T m ell (S f):=LinearMap.congr_fun hc.eq f
  unfold normalizedState phiResponseCore
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,he,hi]


/-- One N and one cofinal source event pay every physical clock in the source-owned window,
all noises, and both causal restrictions of the same full scalar Noether update. -/
theorem actual_corrected_scalar_noether_common_payment (half : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced : Bool, ∀ s:ℝ, ∀ hs:0<s, s ≤ scalarClockWindow half → ∀ ξ η:ℝ,
      (∫⁻x:ℝ,ENNReal.ofReal (correctedScalarNoetherGap s hs ξ η half advanced m ell F x g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c:=scalarNoetherNormCost half
  have hc:0 ≤ c:=norm_cost_nonnegative half
  have hd:0<ε/(c+1):=div_pos hε (by positivity)
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail (sourceNoetherFrequency half)
    (frequency_pos half) g (ε/(c+1)) hd
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced s hs ht ξ η
  have hn:=hF advanced
  have hp(x:ℝ):‖embed (normalizedState m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)‖^2=
      normalizedEnergy m ell F (actualFrequency advanced (sourceNoetherFrequency half) x)
        (frequency_nonreal half advanced x) g := by
    rw [normalized_return]
    rfl
  calc
    _  ≤  ∫⁻x:ℝ,ENNReal.ofReal (c*normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal ((actual_corrected_scalar_noether_point_payment s hs ξ η half advanced ht m ell F x g).trans_eq (by rw [hp]))
    _ = ENNReal.ofReal c*(∫⁻x:ℝ,ENNReal.ofReal (normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)) := by
      simp_rw [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _  ≤  ENNReal.ofReal c*ENNReal.ofReal (ε/(c+1)) := mul_le_mul_of_nonneg_left hn zero_le
    _  ≤  ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0<c+1 by positivity)).mpr
      nlinarith only [hc,hε]

def correctedScalarAbsorbedRemainder (u:QuantumTest)(z:ℂ):ℝ:=
  remainingNativeField u+(35*n/96)*‖embed (inverseVolumeAction (combinedGenerator u))‖^2+
    (432/n)*‖embed (covariantKinetic u-z • u)‖^2-
    (n/48)*‖embed (matchedTester u)+((144/n:ℝ):ℂ) • embed (covariantKinetic u-z • u)‖^2-
    10*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u

def correctedScalarAbsorptionGap (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let u:=K s hs ξ η (normalizedState m ell F z hz g)
  updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
    (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      correctedScalarAbsorbedRemainder u z)
private theorem corrected_absorption_return (s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):
    correctedScalarAbsorptionGap s hs ξ η half advanced m ell F x g=
      correctedScalarNoetherGap s hs ξ η half advanced m ell F x g:=by
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  let u:=K s hs ξ η w
  have h:=actual_corrected_R_coframe_source s hs (ξ,η) m ell F z hz g
  dsimp only at h
  change updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g=
    (sourcePair u (completeCurrent nativeComplement u)).re+matchedField u+
    (35*n/96)*‖embed (inverseVolumeAction (combinedGenerator u))‖^2+
    (432/n)*‖embed (coframeForcing s hs (ξ,η) z w)‖^2-
    (n/48)*‖embed (coframeCompleted s hs (ξ,η) z w)‖^2 at h
  rw [actual_native_field_scalar_split] at h
  unfold correctedScalarAbsorptionGap correctedScalarNoetherGap
  change updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
    (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      correctedScalarAbsorbedRemainder u z)=
    scalarNativePrice u-scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u
  rw [h]
  simp only [coframeForcing,coframeCompleted,map_add,map_smul,correctedScalarAbsorbedRemainder]
  dsimp only [u,w,K]
  ring

/-- The actual complete corrected R directly consumes this clock-uniform source payment.
Its full remaining field and coframe forcing square keep their original signs. -/
theorem actual_corrected_R_scalar_noether_payment (half:Bool)(g:diagonal.domain):
    ∀ ε:ℝ,0<ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,∀ s:ℝ,∀ hs:0<s,
      s ≤ scalarClockWindow half → ∀ ξ η:ℝ,
      (∫⁻x:ℝ,ENNReal.ofReal (correctedScalarAbsorptionGap s hs ξ η half advanced m ell F x g)) ≤ ENNReal.ofReal ε:=by
  simpa only [corrected_absorption_return] using actual_corrected_scalar_noether_common_payment half g
end LowEnergy.FirstCurrentJointBudget
