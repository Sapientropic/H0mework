import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeCarrierElectric
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianMeanSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeCarrier
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentElectricSuccessor FirstCurrentPayerNext
open ClockPhiMatchedGainFrequencyPayment ClockPhiCorrectedGaussianMeanSource
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev A:=SourceClockPhiCombinedScalePressure.combinedConjugate
attribute [local irreducible] diagonalAction sourcePair embed normalizedState normalizedForcing
  correctedCompleteCore wholeSourceNext
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hg:=actual_source_noether_gap half
  linarith
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

private theorem complete_mean_second_price(t:ℝ)(ht:0<t)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖ ≤
      ‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖*‖embed h‖:=by
  let v:=embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  let B:=ClockPhiHeatSecondNativeSource.heatASecondReader t ht
  have he:inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))=inner ℂ (B v) (embed h):=by
    simpa only[correctedCompleteCore,Module.End.mul_apply] using
      (actual_corrected_mean_A_squared_source t ht (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).2 h
  have hn:‖B v‖ ≤ (1/t)*‖v‖:=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (ClockPhiHeatSecondNativeSource.actual_heat_second_native_source t ht).1 (norm_nonneg _))
  have hb:t*‖B v‖ ≤ ‖v‖:=by
    calc _ ≤ t*((1/t)*‖v‖):=mul_le_mul_of_nonneg_left hn ht.le
         _=‖v‖:=by field_simp [ht.ne']
  rw [he]
  calc
    _ ≤ t*(‖B v‖*‖embed h‖):=mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ht.le
    _=(t*‖B v‖)*‖embed h‖:=by ring
    _ ≤ ‖v‖*‖embed h‖:=mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem complete_mean_small_time_price(t:ℝ)(ht:0<t)(ht1:t ≤ 1)(η:ℝ)(hη:0<η)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖ ≤ η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+
        2*η*‖embed f‖^2+‖embed h‖^2/(4*η):=by
  let G:=‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖
  let H:=‖embed h‖
  have hG:=SourceClockPhiCompleteHeatGainPayment.actual_complete_heat_gain_payment t ht 1 (by norm_num) 0 f
  change ‖embed (sourceHeatCore t ht 0 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))‖^2 ≤ _ at hG
  rw [sourceHeat_norm] at hG
  have hG':G^2 ≤ SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+2*‖embed f‖^2:=by
    dsimp only [G]
    norm_num only [one_mul,div_one] at hG
    have ht2:t^2 ≤ 1:=by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg ‖embed f‖)]
  have hy:G*H ≤ η*G^2+H^2/(4*η):=by
    have he:(4*η)*(η*G^2+H^2/(4*η))=4*η^2*G^2+H^2:=by
      field_simp [hη.ne']
    have hh:(4*η)*(G*H) ≤ (4*η)*(η*G^2+H^2/(4*η)):=by
      rw [he]
      nlinarith [sq_nonneg (2*η*G-H)]
    exact (mul_le_mul_iff_right₀ (by positivity:0<4*η)).mp hh
  have he:=mul_le_mul_of_nonneg_left hG' hη.le
  have hP:=complete_mean_second_price t ht f h
  change _ ≤ G*H at hP
  dsimp only [H] at hy
  nlinarith

private theorem frequency_norm_floor(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    μ ≤ ‖actualFrequency advanced μ freq‖:=by
  have h:=Complex.abs_im_le_norm (actualFrequency advanced μ freq)
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,abs_neg,abs_of_pos hμ] using h


private abbrev X:=FirstCurrentGeometricPayer.weightedElectricCurrent
private theorem energy_nonnegative(w:QuantumTest):0≤SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w:=by
  unfold SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
  positivity
private theorem graph_nonnegative(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    0≤wholeGraphDensity half advanced m ell F g q:=by
  dsimp only[wholeGraphDensity]
  have he:=energy_nonnegative (X (frequencyState half advanced m ell F g q))
  positivity
private theorem norm_add_square(a b:H):‖a+b‖^2≤2*‖a‖^2+2*‖b‖^2:=by
  have h:=pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith only[h,sq_nonneg (‖a‖-‖b‖)]
private theorem norm_update(h:ℝ)(w v:QuantumTest):
    ‖embed (w+(h:ℂ) • v)‖^2≤2*‖embed w‖^2+2*h^2*‖embed v‖^2:=by
  have hn:=norm_add_square (embed w) ((h:ℂ) • embed v)
  simpa only[map_add,map_smul,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_assoc] using hn
private theorem energy_update(h:ℝ)(w v:QuantumTest):
    SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy (w+(h:ℂ) • v)≤
      2*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w+
      2*h^2*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy v:=by
  have hB:=norm_update h (SourceClockPhiMatchedDiffusionSource.driftClock w) (SourceClockPhiMatchedDiffusionSource.driftClock v)
  have hD:=norm_update h (SourcePhysicalKineticSquare.inverseVolumeAction (SourceClockPhiCombinedScalePressure.combinedGenerator w))
    (SourcePhysicalKineticSquare.inverseVolumeAction (SourceClockPhiCombinedScalePressure.combinedGenerator v))
  unfold SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
  simp only[map_add,map_smul] at hB hD ⊢
  nlinarith only[hB,hD]
private def paymentEnvelope(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(η q:ℝ):ℝ:=
  let w:=frequencyState half advanced m ell F g q
  2*η*‖embed w‖^2+(1/η)*‖embed (actualFrequency advanced (sourceNoetherFrequency half) q • w)‖^2+
    (η+1/η)*(wholeStep s hs half advanced m ell F g)^2*wholeGraphDensity half advanced m ell F g q
private theorem point_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)
    (η:ℝ)(hη:0<η)(τ:ℝ)(hτ:0<τ)(hτ1:τ≤1)(q:ℝ):
    let b:=wholeSourceNext s hs half advanced m ell F g q
    τ*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2 b.1) ∂γ.prod γ)
      (embed ((A*A) (diagonalAction b.1-b.2)))‖-
      η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy (frequencyState half advanced m ell F g q)≤
        paymentEnvelope s hs half advanced m ell F g η q:=by
  dsimp only
  let b:=wholeSourceNext s hs half advanced m ell F g q
  let w:=frequencyState half advanced m ell F g q
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let h:=wholeStep s hs half advanced m ell F g
  have hb:b.1=w+(h:ℂ) • X w:=by
    unfold b wholeSourceNext
    rfl
  have hsource:diagonalAction b.1=b.2+z • b.1:=
    ((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.1
  have he:diagonalAction b.1-b.2=z • b.1:=by rw [hsource];module
  have hp:=complete_mean_small_time_price τ hτ hτ1 (η/2) (by positivity) b.1 (z • b.1)
  have hE:=energy_update h w (X w)
  have hn:=norm_update h w (X w)
  have hz:=norm_update h (z • w) (z • X w)
  have hzw:z • b.1=z • w+(h:ℂ) • (z • X w):=by rw [hb,smul_add,smul_comm z (h:ℂ)]
  have hEp:=mul_le_mul_of_nonneg_left hE (by positivity:0≤η/2)
  have hnp:=mul_le_mul_of_nonneg_left hn hη.le
  have hzp:=div_le_div_of_nonneg_right hz (by positivity:0≤4*(η/2))
  rw [hzw,hb] at hp
  have hpositive:0≤h^2*((1/η)*(2*‖embed (X w)‖^2+
      SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy (X w))+η*‖embed (z • X w)‖^2):=by
    have heX:=energy_nonnegative (X w)
    positivity
  change τ*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2 b.1) ∂γ.prod γ)
    (embed ((A*A) (diagonalAction b.1-b.2)))‖-η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w≤_
  rw [he]
  change _≤2*η*‖embed w‖^2+(1/η)*‖embed (z • w)‖^2+
    (η+1/η)*h^2*(2*‖embed (X w)‖^2+SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy (X w)+‖embed (z • X w)‖^2)
  rw [hzw,hb]
  have hden:(2*‖embed (z • w)‖^2+2*h^2*‖embed (z • X w)‖^2)/(4*(η/2))=
      (1/η)*‖embed (z • w)‖^2+(1/η)*h^2*‖embed (z • X w)‖^2:=by ring
  nlinarith only[hp,hEp,hnp,hzp,hpositive,hden]
private theorem norm_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun q:ℝ=>‖embed (frequencyState half advanced m ell F g q)‖^2):=by
  have hp:=(SourceClockPhiWholeSignedWorkIntegrable.actual_normalized_pair_integrable
    (sourceNoetherFrequency half) (frequency_positive half) advanced m ell F g 1 1).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  simpa only[Module.End.one_apply,he,RCLike.re_eq_complex_re,frequencyState] using hp
private theorem envelope_nonnegative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)
    (η:ℝ)(hη:0<η)(q:ℝ):0≤paymentEnvelope s hs half advanced m ell F g η q:=by
  dsimp only[paymentEnvelope]
  have hG:=graph_nonnegative half advanced m ell F g q
  positivity
private theorem envelope_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)
    (η:ℝ)(hη:0<η):
    Integrable (paymentEnvelope s hs half advanced m ell F g η) ∧
    (∫q:ℝ,paymentEnvelope s hs half advanced m ell F g η q)≤
      ((3*η+1/η)/(sourceNoetherFrequency half)^2+1/η)*
        (∫q:ℝ,‖embed (actualFrequency advanced (sourceNoetherFrequency half) q •
          frequencyState half advanced m ell F g q)‖^2):=by
  let μ:=sourceNoetherFrequency half
  let W:=wholeNormPrice half advanced m ell F g
  let Z:=∫q:ℝ,‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2
  let P:=wholeGraphPrice half advanced m ell F g
  let h:=wholeStep s hs half advanced m ell F g
  have hμ:0<μ:=frequency_positive half
  have hW:=norm_integrable half advanced m ell F g
  have hZ:Integrable (fun q:ℝ=>‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2):=
    actual_whole_carrier_shifted_square half advanced m ell F g 1
  have hP:=(actual_whole_electric_graph_payment s hs half advanced m ell F g).1
  have hi:Integrable (paymentEnvelope s hs half advanced m ell F g η):=
    ((hW.const_mul (2*η)).add (hZ.const_mul (1/η))).add (hP.const_mul ((η+1/η)*h^2))
  refine ⟨hi,?_⟩
  have hWpos:0≤W:=integral_nonneg (fun _=>sq_nonneg _)
  have hfloor(q:ℝ):‖embed (frequencyState half advanced m ell F g q)‖^2≤
      (1/μ^2)*‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2:=by
    have hn:=mul_le_mul_of_nonneg_right (frequency_norm_floor advanced μ hμ q)
      (norm_nonneg (embed (frequencyState half advanced m ell F g q)))
    have hh:=pow_le_pow_left₀ (by positivity:0≤μ*‖embed (frequencyState half advanced m ell F g q)‖) hn 2
    rw [map_smul,norm_smul]
    calc _≤(‖actualFrequency advanced μ q‖*‖embed (frequencyState half advanced m ell F g q)‖)^2/μ^2:=
      (le_div_iff₀ (sq_pos_of_pos hμ)).mpr (by nlinarith only[hh])
         _= _:=by ring
  have hWbound:W≤(1/μ^2)*Z:=by
    have hi:=integral_mono hW (hZ.const_mul (1/μ^2)) hfloor
    simpa only[integral_const_mul,W,Z,wholeNormPrice] using hi
  have hstep:h^2*P≤W:=by
    have hp:=(actual_whole_electric_graph_payment s hs half advanced m ell F g).2
    change h^2*P≤W/4 at hp
    linarith only[hp,hWpos]
  have hsprice:=mul_le_mul_of_nonneg_left hstep (by positivity:0≤η+1/η)
  have hnprice:=mul_le_mul_of_nonneg_left hWbound (by positivity:0≤3*η+1/η)
  change (∫q:ℝ,2*η*‖embed (frequencyState half advanced m ell F g q)‖^2+
    (1/η)*‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2+
    ((η+1/η)*h^2)*wholeGraphDensity half advanced m ell F g q)≤_
  erw [integral_add ((hW.const_mul (2*η)).add (hZ.const_mul (1/η))) (hP.const_mul ((η+1/η)*h^2)),
    integral_add (hW.const_mul (2*η)) (hZ.const_mul (1/η)),integral_const_mul,integral_const_mul,integral_const_mul]
  change 2*η*W+(1/η)*Z+((η+1/η)*h^2)*P≤((3*η+1/η)/μ^2+1/η)*Z
  have heq:((3*η+1/η)/μ^2+1/η)*Z=(3*η+1/η)*((1/μ^2)*Z)+(1/η)*Z:=by ring
  rw [heq]
  nlinarith only[hsprice,hnprice]

/-- The whole fixed-pole update consumes the original Ec debit on a common source tail.
No frequency-adapted coefficient, graph budget, or division by tau enters this payment. -/
theorem actual_whole_electric_original_Ec_common_payment(half:Bool)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,∀τ:ℝ,∀hτ:0<τ,τ ≤ 1 →
      (∫⁻q:ℝ,ENNReal.ofReal (τ*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2
          (wholeSourceNext s hs half advanced m ell F g q).1) ∂γ.prod γ)
        (embed ((A*A) (diagonalAction (wholeSourceNext s hs half advanced m ell F g q).1-
          (wholeSourceNext s hs half advanced m ell F g q).2)))‖-
        η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
          (frequencyState half advanced m ell F g q))) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  have hμ:0<μ:=frequency_positive half
  let C:ℝ:=(3*η+1/η)/μ^2+1/η
  have hC:0≤C:=by dsimp[C];positivity
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced s hs τ hτ hτ1
  have hp:=envelope_payment s hs half advanced m ell F g η hη
  have hZ:Integrable (fun q:ℝ=>‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2):=
    actual_whole_carrier_shifted_square half advanced m ell F g 1
  calc
    _≤∫⁻q:ℝ,ENNReal.ofReal (paymentEnvelope s hs half advanced m ell F g η q):=by
      apply lintegral_mono
      intro q
      exact ENNReal.ofReal_le_ofReal (point_payment s hs half advanced m ell F g η hη τ hτ hτ1 q)
    _=ENNReal.ofReal (∫q:ℝ,paymentEnvelope s hs half advanced m ell F g η q):=
      (ofReal_integral_eq_lintegral_ofReal hp.1 (Eventually.of_forall (envelope_nonnegative s hs half advanced m ell F g η hη))).symm
    _≤ENNReal.ofReal (C*(∫q:ℝ,‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2)):=
      ENNReal.ofReal_le_ofReal hp.2
    _=ENNReal.ofReal C*(∫⁻q:ℝ,ENNReal.ofReal (‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2)):=by
      rw [ENNReal.ofReal_mul hC,ofReal_integral_eq_lintegral_ofReal hZ (Eventually.of_forall (fun _=>sq_nonneg _))]
    _≤ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)):=by
      apply mul_le_mul_of_nonneg_left _ zero_le
      have he(q:ℝ):actualFrequency advanced μ q • frequencyState half advanced m ell F g q=
          shiftedState m ell F (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g:=
        (hS m ell _ (frequency_nonreal half advanced q)).1
      simpa only[he] using hF advanced
    _≤ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      exact (div_le_iff₀ (by positivity:C+1>0)).mpr (by nlinarith)
/-- The original starting physical price is returned from the same admissible whole-carrier update,
with a source-generated common upper error before either cause and every positive clock. -/
theorem actual_starting_physical_mean_common_return(half:Bool)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,
      (∫q:ℝ,physicalMean s hs half advanced q (frequencyState half advanced m ell F g q))≤
        (∫q:ℝ,∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
          (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ)+ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  have hμ:0<μ:=frequency_positive half
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (2*ε*μ^2) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced s hs
  have hW:=norm_integrable half advanced m ell F g
  have hZ:Integrable (fun q:ℝ=>‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2):=
    actual_whole_carrier_shifted_square half advanced m ell F g 1
  have hZbound:(∫q:ℝ,‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2)≤2*ε*μ^2:=by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity:0≤2*ε*μ^2)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hZ (Eventually.of_forall (fun _=>sq_nonneg _))]
    have he(q:ℝ):actualFrequency advanced μ q • frequencyState half advanced m ell F g q=
        shiftedState m ell F (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g:=
      (hS m ell _ (frequency_nonreal half advanced q)).1
    simpa only[he] using hF advanced
  have hpoint(q:ℝ):μ^2*‖embed (frequencyState half advanced m ell F g q)‖^2≤
      ‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2:=by
    have hn:=mul_le_mul_of_nonneg_right (frequency_norm_floor advanced μ hμ q)
      (norm_nonneg (embed (frequencyState half advanced m ell F g q)))
    have hh:=pow_le_pow_left₀ (by positivity:0≤μ*‖embed (frequencyState half advanced m ell F g q)‖) hn 2
    rw [map_smul,norm_smul]
    nlinarith only[hh]
  have hn:=integral_mono (hW.const_mul (μ^2)) hZ hpoint
  rw [integral_const_mul] at hn
  change μ^2*wholeNormPrice half advanced m ell F g≤_ at hn
  have hnorm:wholeNormPrice half advanced m ell F g/2≤ε:=by
    nlinarith only[hn,hZbound,sq_pos_of_pos hμ]
  have hp:=(actual_whole_electric_mean_payment s hs half advanced m ell F g).2
  exact hp.trans (by linarith only[hnorm])
end LowEnergy.FirstCurrentWholeCarrier
