import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiRemainingFieldSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudgetNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceClockReflectedForm SourceScalarVirialBulk
open SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusNormalizedFluxBudget SourceClockPhiRadiusSourceCurrent
open SourceClockRadiusAffineCutoff SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy FullYSourceResolventGraphSplice
open ClockPhiHeatCorrectedCovarianceSource SourceCoframeCovariantAction NativePointReturn
open FirstCurrentJointBudget FirstCurrentPayerNext FinitePhysicalSource MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev D : End := combinedGenerator
private abbrev Dc : End := dilation
private abbrev M : End := matchedTester
private abbrev K := correctedCompleteCore
attribute [local irreducible] sourcePair embed normalizedState normalizedForcing diagonalAction correctedCompleteCore updatedForcing
  coframeForcing coframeCompleted completeCurrent nativeComplement matchedTester combinedConjugate
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_pos(half:Bool):0<sourceNoetherFrequency half:=by
  linarith [actual_source_noether_gap half,n_pos]
private theorem frequency_nonreal(half advanced:Bool)(x:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0:=by
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using (frequency_pos half).ne'
private theorem norm_cost_nonnegative(half:Bool):0 ≤ scalarNoetherNormCost half:=by
  unfold scalarNoetherNormCost
  have hn:=n_pos
  have hk:=(actual_scalar_noether_fraction half).1
  positivity

def jointClockWindow(half:Bool):ℝ:=min (scalarClockWindow half) (61/432)
theorem actual_joint_clock_window_positive(half:Bool):0<jointClockWindow half:=
  lt_min (actual_scalar_clock_window_positive half) (by norm_num)

/-- The source's remaining shifted squares pay the exact 72n full-clock norm created by the local field. -/
theorem actual_remaining_clock_norm_payment(s:ℝ)(hs:0<s)(ht:s ≤ 61/432)(ξ η:ℝ)(w:QuantumTest):
    let u:=K s hs ξ η w
    72*n*‖embed u‖^2-3*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u ≤ 72*n*‖embed w‖^2:=by
  dsimp only
  have hn:=n_pos
  have hc:0 ≤ 72*n:=by positivity
  have hb:18*s*(72*n) ≤ 183*n:=by
    nlinarith [mul_le_mul_of_nonneg_right ht hn.le]
  have hG:=actual_corrected_scalar_gain_mass_payment (72*n) hc s hs hb ξ η w
  have hU:=mul_le_mul_of_nonneg_left (actual_scalar_payment_uncertainty (K s hs ξ η w))
    (show 0 ≤ 3*n by positivity)
  nlinarith only[hG,hU]

def remainingGeometricPrice(u:QuantumTest)(z:ℂ):ℝ:=
  3*n*reflectedForm (U u)+10*gaugeForm (U u)+4*(sourcePair u (U (magneticAction u))).re-
    (9*n/4)*(sourcePair (U (D u)) (Dc (U u))).im+(35*n/96)*‖embed (U (D u))‖^2+
    6*(sourcePair (M u) (z • u)).re-(n/48)*‖embed (M u)‖^2-7*n*inverseNativeEnergy u
private theorem density_price_split(u:QuantumTest)(z:ℂ):
    densityFreeRemainder u z=remainingGeometricPrice u z+
      (72*n*‖embed u‖^2-3*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u):=by
  unfold densityFreeRemainder remainingGeometricPrice
  ring

private theorem corrected_R_return(s:ℝ)(hs:0<s)(ξ η:ℝ)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    let u:=K s hs ξ η (normalizedState m ell F z hz g)
    updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g=
      scalarNativePrice u+densityFreeRemainder u z+10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u:=by
  dsimp only
  let w:=normalizedState m ell F z hz g
  let u:=K s hs ξ η w
  have h:=actual_corrected_R_coframe_source s hs (ξ,η) m ell F z hz g
  dsimp only at h
  change updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g=
    (sourcePair u (completeCurrent nativeComplement u)).re+matchedField u+
    (35*n/96)*‖embed (U (D u))‖^2+(432/n)*‖embed (coframeForcing s hs (ξ,η) z w)‖^2-
      (n/48)*‖embed (coframeCompleted s hs (ξ,η) z w)‖^2 at h
  rw [actual_native_field_scalar_split] at h
  rw [h,←actual_density_free_remainder]
  simp only[correctedScalarAbsorbedRemainder,coframeForcing,coframeCompleted,map_add,map_smul]
  dsimp only[u,w,K]
  ring

def remainingGeometricGap(s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)(m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let u:=K s hs ξ η (normalizedState m ell F z hz g)
  updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
    (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      remainingGeometricPrice u z)

/-- Both original scalar-square reserves jointly pay the actual complete clock update.
The remaining geometric price has no spin, Number, density, shifted-field or gained-norm price. -/
theorem actual_remaining_geometric_point_payment(s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (ht:s ≤ jointClockWindow half)(m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):
    remainingGeometricGap s hs ξ η half advanced m ell F x g ≤
      (scalarNoetherNormCost half+72*n)*‖embed (normalizedState m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)‖^2:=by
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  let u:=K s hs ξ η w
  have hS:=actual_corrected_scalar_noether_point_payment s hs ξ η half advanced
    (ht.trans (min_le_left _ _)) m ell F x g
  have hG:=actual_remaining_clock_norm_payment s hs (ht.trans (min_le_right _ _)) ξ η w
  have hR:=corrected_R_return s hs ξ η m ell F z hz g
  dsimp only at hR hG
  rw [density_price_split] at hR
  change scalarNativePrice u-scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
    10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u ≤ scalarNoetherNormCost half*‖embed w‖^2 at hS
  change remainingGeometricGap s hs ξ η half advanced m ell F x g ≤ (scalarNoetherNormCost half+72*n)*‖embed w‖^2
  unfold remainingGeometricGap
  change updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
    (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      remainingGeometricPrice u z) ≤ _
  change updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g=scalarNativePrice u+
    (remainingGeometricPrice u z+(72*n*‖embed u‖^2-3*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u))+
    10*n*inverseNativeEnergy u+3*n*scalarPaymentSquare u at hR
  change 72*n*‖embed u‖^2-3*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u ≤ 72*n*‖embed w‖^2 at hG
  nlinarith only[hS,hG,hR]

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


/-- One common N and cofinal event pay all clocks in the fixed joint window and both actual noises/causes. -/
theorem actual_remaining_geometric_common_payment (half : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced : Bool,∀ s:ℝ,∀ hs:0<s,s ≤ jointClockWindow half → ∀ ξ η:ℝ,
      (∫⁻x:ℝ,ENNReal.ofReal (remainingGeometricGap s hs ξ η half advanced m ell F x g))≤ENNReal.ofReal ε := by
  intro ε hε
  let c:=scalarNoetherNormCost half+72*n
  have hc:0≤c:=by dsimp only[c];have hn:=n_pos;have hcost:=norm_cost_nonnegative half;positivity
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
    _ ≤ ∫⁻x:ℝ,ENNReal.ofReal (c*normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal ((actual_remaining_geometric_point_payment s hs ξ η half advanced ht m ell F x g).trans_eq (by rw [hp]))
    _ = ENNReal.ofReal c*(∫⁻x:ℝ,ENNReal.ofReal (normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)) := by
      simp_rw [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c*ENNReal.ofReal (ε/(c+1)) := mul_le_mul_of_nonneg_left hn zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0<c+1 by positivity)).mpr
      nlinarith only [hc,hε]
end LowEnergy.FirstCurrentJointBudgetNext
