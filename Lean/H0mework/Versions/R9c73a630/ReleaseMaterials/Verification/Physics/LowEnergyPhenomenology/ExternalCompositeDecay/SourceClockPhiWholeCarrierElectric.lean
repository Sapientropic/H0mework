import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFrequencyPhysicalMean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.FirstCurrentWholeCarrier
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceInverseJetEnergy FullYSourceResolventGraphSplice SourceInverseNoetherChannelGap SourceInverseElectricMomentChannels
open SourceClockPhiWholeSignedWorkIntegrable ClockPhiCorrectedPhysicalWorkAbel
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open FirstCurrentJointBudget FirstCurrentGeometricPayer FirstCurrentElectricSuccessor FirstCurrentPayerNext
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian FirstCurrentOriginalEcPayer
open FinitePhysicalSource SourceClockPhiNativeJointPayment MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev X:End:=weightedElectricCurrent
private abbrev U:End:=SourcePhysicalKineticSquare.inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] diagonalAction embed normalizedState normalizedForcing sourcePair resolventCore compressionCore
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
private theorem original_state_seed(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    state F z hz g=resolventCore F z hz (coreEquiv.symm g):=by
  simp only[resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private theorem source_column_return(L:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    L (normalizedState m ell F z hz g)=
      ∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • sourceColumn L m ell F g j:=by
  have hs:normalizedState m ell F z hz g=
      ∑i:Fin 2,phaseRow m ell i (state F z hz (inputSeed g i)):=by
    simp only[Fin.sum_univ_two]
    change normalizedState m ell F z hz g=
      phiThetaAction m ell (state F z hz g)+
        (-(phiInverseAction*phiThetaAction m ell) (state F z hz (phiRadiusSource g)))
    rw [original_state_seed F z hz g,original_state_seed F z hz (phiRadiusSource g)]
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
    simp only[normalizedState,Module.End.mul_apply]
    module
  rw [hs]
  simp_rw [actual_state_channels,map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only[sourceColumn,Finset.smul_sum]
private theorem shifted_column_return(L:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    z • L (normalizedState m ell F z hz g)=
      ∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • ((channelValue F j:ℂ) • sourceColumn L m ell F g j):=by
  rw [source_column_return,Finset.smul_sum]
  have he(j:Channel F):z*((channelValue F j:ℂ)-z)⁻¹=
      ((channelValue F j:ℂ)-z)⁻¹*(channelValue F j:ℂ)-1:=by
    have hn:((channelValue F j:ℂ)-z)≠0:=by
      intro h
      have hi:=congrArg Complex.im h
      simp only[Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
      exact hz hi
    field_simp [hn]
    ring
  simp only[smul_smul,he,sub_smul,one_smul,Finset.sum_sub_distrib,actual_source_column_zero,sub_zero]
private theorem series_norm_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(c:Channel F→QuantumTest):
    Integrable (fun q:ℝ=>‖embed (∑j:Channel F,((channelValue F j:ℂ)-
      actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹ • c j)‖^2):=by
  have hp(i j:Channel F):Integrable (fun q:ℝ=>
      star (((channelValue F i:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹)*
      ((channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹*sourcePair (c i) (c j)):=by
    have h:=(actual_linear_physical_work_source (1:End) (sourceNoetherFrequency half) (frequency_positive half)
      advanced m ell F g).2.2.1 (channelValue F i) (channelValue F j)
    exact h.1.mul_const _
  have h:=integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun i (_:i∈Finset.univ)=>
    integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun j (_:j∈Finset.univ)=>hp i j))
  have he(q:ℝ):sourcePair (∑j:Channel F,((channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹ • c j)
      (∑j:Channel F,((channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹ • c j)=
      ∑i:Channel F,∑j:Channel F,
        star (((channelValue F i:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹)*
        ((channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹*sourcePair (c i) (c j):=by
    simp only[sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only[starRingEnd_apply]
    ring
  apply h.re.congr
  exact Eventually.of_forall (fun q=>by
    simp only[RCLike.re_eq_complex_re]
    rw [←he]
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) _)

/-- Every transformed leg retains the original pole carrier; its shifted square is paid internally. -/
theorem actual_whole_carrier_shifted_square(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>‖embed (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q))‖^2):=by
  have h:=series_norm_integrable half advanced m ell F g (fun j:Channel F=>(channelValue F j:ℂ) • sourceColumn L m ell F g j)
  apply h.congr
  exact Eventually.of_forall (fun q=>by
    dsimp only
    rw [←shifted_column_return L m ell F _ (frequency_nonreal half advanced q) g]
    rfl)
private theorem word_norm_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (frequencyState half advanced m ell F g q))‖^2):=by
  have hp:=(actual_normalized_pair_integrable (sourceNoetherFrequency half) (frequency_positive half) advanced m ell F g L L).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  simpa only[he,RCLike.re_eq_complex_re,frequencyState] using hp
private theorem energy_nonnegative(w:QuantumTest):0≤comparisonEnergy w:=by unfold comparisonEnergy;positivity
private theorem energy_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>comparisonEnergy (L (frequencyState half advanced m ell F g q))):=
  (word_norm_integrable half advanced m ell F g (driftClock*L)).add
    ((word_norm_integrable half advanced m ell F g (U*D*L)).const_mul (1/2:ℝ))
def wholeGraphDensity(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):ℝ:=
  let w:=frequencyState half advanced m ell F g q
  2*‖embed (X w)‖^2+comparisonEnergy (X w)+
    ‖embed (actualFrequency advanced (sourceNoetherFrequency half) q • X w)‖^2
def wholeGraphPrice(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  ∫q:ℝ,wholeGraphDensity half advanced m ell F g q
def wholeNormPrice(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  ∫q:ℝ,‖embed (frequencyState half advanced m ell F g q)‖^2
def wholeSlope(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  ∫q:ℝ,physicalMean s hs half advanced q ((1+X) (frequencyState half advanced m ell F g q))-
    physicalMean s hs half advanced q (frequencyState half advanced m ell F g q)-
    physicalMean s hs half advanced q (X (frequencyState half advanced m ell F g q))
def wholeCurvature(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  ∫q:ℝ,physicalMean s hs half advanced q (X (frequencyState half advanced m ell F g q))
def wholeFraction(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  wholeNormPrice half advanced m ell F g /
    ((|wholeSlope s hs half advanced m ell F g|+1)*
      (wholeNormPrice half advanced m ell F g+wholeGraphPrice half advanced m ell F g+
        |wholeSlope s hs half advanced m ell F g|+|wholeCurvature s hs half advanced m ell F g|+1))
def wholeStep(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  (-wholeSlope s hs half advanced m ell F g/(2*(|wholeCurvature s hs half advanced m ell F g|+1)))*
    wholeFraction s hs half advanced m ell F g
def wholeSourceMap(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):End:=
  1+(wholeStep s hs half advanced m ell F g:ℂ) • X
def wholeSourceNext(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):QuantumTest×QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let a:QuantumTest×QuantumTest:=(frequencyState half advanced m ell F g q,
    normalizedForcing m ell F z (frequency_nonreal half advanced q) g)
  a+(wholeStep s hs half advanced m ell F g:ℂ) • electricSourceDirection a
private theorem norm_nonnegative(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    0≤wholeNormPrice half advanced m ell F g:=integral_nonneg (fun _=>sq_nonneg _)
private theorem graph_nonnegative(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    0≤wholeGraphPrice half advanced m ell F g:=by
  apply integral_nonneg
  intro q
  dsimp only[wholeGraphDensity]
  have he:=energy_nonnegative (X (frequencyState half advanced m ell F g q))
  positivity
private theorem graph_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (wholeGraphDensity half advanced m ell F g):=
  (((word_norm_integrable half advanced m ell F g X).const_mul 2).add
    (energy_integrable half advanced m ell F g X)).add (actual_whole_carrier_shifted_square half advanced m ell F g X)
private theorem whole_fraction_interval(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    0≤wholeFraction s hs half advanced m ell F g ∧ wholeFraction s hs half advanced m ell F g≤1:=by
  have hW:=norm_nonnegative half advanced m ell F g
  have hG:=graph_nonnegative half advanced m ell F g
  unfold wholeFraction
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    have hA:=abs_nonneg (wholeSlope s hs half advanced m ell F g)
    have hC:=abs_nonneg (wholeCurvature s hs half advanced m ell F g)
    nlinarith [mul_nonneg hA (show 0≤wholeNormPrice half advanced m ell F g+
      wholeGraphPrice half advanced m ell F g+|wholeSlope s hs half advanced m ell F g|+
        |wholeCurvature s hs half advanced m ell F g|+1 by positivity)]

/-- A single coefficient is fixed before every frequency and both Gaussian coordinates.
It retains the original poles, zero column, full forcing and every corrected-clock restriction. -/
theorem actual_whole_electric_source_carrier(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    let L:=wholeSourceMap s hs half advanced m ell F g
    (∑j:Channel F,sourceColumn L m ell F g j)=0 ∧
    ∀q:ℝ,let z:=actualFrequency advanced (sourceNoetherFrequency half) q
      let b:=wholeSourceNext s hs half advanced m ell F g q
      b.1=(∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • sourceColumn L m ell F g j) ∧
      diagonalAction b.1=b.2+z • b.1 ∧
      ∀x:ℝ×ℝ,diagonalAction (clockSourcePair s hs x b).1=
        (clockSourcePair s hs x b).2+z • (clockSourcePair s hs x b).1:=by
  dsimp only
  refine ⟨actual_source_column_zero _ _ _ _ _,fun q=>?_⟩
  constructor
  · exact source_column_return (wholeSourceMap s hs half advanced m ell F g) m ell F _
      (frequency_nonreal half advanced q) g
  · have hp(x:ℝ×ℝ):=actual_admissible_electric_source_plane s hs m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g 1
      (wholeStep s hs half advanced m ell F g:ℂ) x
    exact ⟨by simpa only[one_smul,wholeSourceNext,frequencyState] using (hp (0,0)).1,fun x=>by simpa only[one_smul,wholeSourceNext,frequencyState] using (hp x).2⟩
private theorem scalar_graph_payment(A C W P:ℝ)(hW:0≤W)(hP:0≤P):
    let h:=(-A/(2*(|C|+1)))*(W/((|A|+1)*(W+P+1)))
    h^2*P≤W/4 ∧ |h|≤1/2 ∧ |h| *P≤W/2:=by
  dsimp only
  let d:=|C|+1
  let e:=(|A|+1)*(W+P+1)
  let h:=(-A/(2*d))*(W/e)
  have hd:0<d:=by dsimp[d];positivity
  have he:0<e:=by dsimp[e];positivity
  have hd1:1≤d:=by dsimp[d];linarith[abs_nonneg C]
  have hAW:|A| *W≤e:=by dsimp[e];nlinarith[mul_nonneg (abs_nonneg A) hP]
  have hAP:|A| *P≤e:=by dsimp[e];nlinarith[mul_nonneg (abs_nonneg A) hW]
  have habs:|h|=|A| *W/(2*d*e):=by
    dsimp only[h]
    rw [abs_mul,abs_div,abs_neg,abs_of_pos (by positivity:0<2*d),abs_div,abs_of_nonneg hW,abs_of_pos he]
    ring
  have hsmall:|h|≤1/2:=by
    rw [habs]
    calc _≤e/(2*d*e):=div_le_div_of_nonneg_right hAW (by positivity)
         _=1/(2*d):=by field_simp[he.ne']
         _≤1/2:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith only[hd1])
  have hlarge:|h| *P≤W/2:=by
    rw [habs]
    have heq:|A| *W/(2*d*e)*P=(|A| *P)*W/(2*d*e):=by ring
    rw [heq]
    calc _≤e*W/(2*d*e):=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAP hW) (by positivity)
         _=W/(2*d):=by field_simp[he.ne']
         _≤W/2:=div_le_div_of_nonneg_left hW (by norm_num) (by nlinarith only[hd1])
  have hm:=mul_le_mul hsmall hlarge (mul_nonneg (abs_nonneg h) hP) (by norm_num:(0:ℝ)≤1/2)
  have heq:|h| *(|h| *P)=h^2*P:=by rw [←mul_assoc,←pow_two,sq_abs]
  rw [heq] at hm
  refine ⟨?_,hsmall,hlarge⟩
  change h^2*P≤W/4
  nlinarith only[hm]

/-- The finite full-frequency graph price generates its own step; it is not an external budget. -/
theorem actual_whole_electric_graph_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (wholeGraphDensity half advanced m ell F g) ∧
    (wholeStep s hs half advanced m ell F g)^2*wholeGraphPrice half advanced m ell F g≤
      wholeNormPrice half advanced m ell F g/4:=by
  refine ⟨graph_integrable half advanced m ell F g,?_⟩
  have hW:=norm_nonnegative half advanced m ell F g
  have hG:=graph_nonnegative half advanced m ell F g
  let A:=wholeSlope s hs half advanced m ell F g
  let C:=wholeCurvature s hs half advanced m ell F g
  let P:=wholeGraphPrice half advanced m ell F g+|A|+|C|
  have hp:=scalar_graph_payment A C (wholeNormPrice half advanced m ell F g) P hW (by dsimp[P];positivity)
  have ht:wholeStep s hs half advanced m ell F g=
      (-A/(2*(|C|+1)))*(wholeNormPrice half advanced m ell F g/((|A|+1)*(wholeNormPrice half advanced m ell F g+P+1))):=by
    unfold wholeStep wholeFraction
    dsimp only[A,C,P]
    congr 4; ring
  rw [ht]
  exact (mul_le_mul_of_nonneg_left (show wholeGraphPrice half advanced m ell F g≤P by dsimp[P];linarith[abs_nonneg A,abs_nonneg C])
    (sq_nonneg _)).trans hp.1
private theorem scalar_descent(A C lam:ℝ)(hlam:0≤lam)(hlam1:lam≤1):
    (-A/(2*(|C|+1))*lam)*A+(-A/(2*(|C|+1))*lam)^2*C≤ -lam*A^2/(4*(|C|+1)):=by
  have hd:0 < |C|+1:=by positivity
  have hC:lam*C≤|C|+1:=by
    calc lam*C≤lam*(|C|+1):=mul_le_mul_of_nonneg_left (by linarith[le_abs_self C]) hlam
         _≤|C|+1:=by nlinarith only[hlam1,hd]
  have h:=mul_le_mul_of_nonneg_left hC (mul_nonneg hlam (sq_nonneg A))
  field_simp [hd.ne']
  nlinarith only[h]
def wholeMeanDebit(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  wholeFraction s hs half advanced m ell F g*(wholeSlope s hs half advanced m ell F g)^2/
    (4*(|wholeCurvature s hs half advanced m ell F g|+1))

/-- The same fixed-pole update generates its exact complete Gaussian-and-frequency physical action.
All coefficient integrals are paid from the original source before the coefficient is selected. -/
theorem actual_whole_electric_physical_action(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    (∀q:ℝ,Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) (γ.prod γ)) ∧
    Integrable (fun q:ℝ=>∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ) ∧
    (∫q:ℝ,∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ)=
      (∫q:ℝ,physicalMean s hs half advanced q (frequencyState half advanced m ell F g q))+
        wholeStep s hs half advanced m ell F g*wholeSlope s hs half advanced m ell F g+
        (wholeStep s hs half advanced m ell F g)^2*wholeCurvature s hs half advanced m ell F g:=by
  let h:=wholeStep s hs half advanced m ell F g
  let pMean(q:ℝ):=physicalMean s hs half advanced q (frequencyState half advanced m ell F g q)
  let cMean(q:ℝ):=physicalMean s hs half advanced q (X (frequencyState half advanced m ell F g q))
  let aMean(q:ℝ):=physicalMean s hs half advanced q ((1+X) (frequencyState half advanced m ell F g q))-pMean q-cMean q
  have hP:Integrable pMean:=actual_physical_mean_frequency_integrable s hs half advanced m ell F g 1
  have hC:Integrable cMean:=actual_physical_mean_frequency_integrable s hs half advanced m ell F g X
  have hA:Integrable aMean:=((actual_physical_mean_frequency_integrable s hs half advanced m ell F g (1+X)).sub hP).sub hC
  have hg(q:ℝ):=actual_source_joint_mean_polynomial s hs half advanced m ell F q h g (frequency_nonreal half advanced q)
  have hc(q:ℝ):=actual_averaged_joint_coefficients s hs half advanced m ell F q g (frequency_nonreal half advanced q)
  have he(q:ℝ):(∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ)=pMean q+h*aMean q+h^2*cMean q:=by
    have heq:=(hg q).2
    rw [(hc q).2.2.1,(hc q).2.2.2] at heq
    exact heq
  have hi:Integrable (fun q:ℝ=>pMean q+h*aMean q+h^2*cMean q):=(hP.add (hA.const_mul h)).add (hC.const_mul (h^2))
  refine ⟨fun q=>(hg q).1,hi.congr (Eventually.of_forall (fun q=>(he q).symm)),?_⟩
  simp_rw [he]
  erw [integral_add (hP.add (hA.const_mul h)) (hC.const_mul (h^2)),integral_add hP (hA.const_mul h),
    integral_const_mul,integral_const_mul]
  rfl
private theorem whole_work_cap(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    |wholeStep s hs half advanced m ell F g*wholeSlope s hs half advanced m ell F g+
      (wholeStep s hs half advanced m ell F g)^2*wholeCurvature s hs half advanced m ell F g|≤
        wholeNormPrice half advanced m ell F g/2:=by
  let A:=wholeSlope s hs half advanced m ell F g
  let C:=wholeCurvature s hs half advanced m ell F g
  let W:=wholeNormPrice half advanced m ell F g
  let P:=wholeGraphPrice half advanced m ell F g+|A|+|C|
  let h:=wholeStep s hs half advanced m ell F g
  have hW:=norm_nonnegative half advanced m ell F g
  have hG:=graph_nonnegative half advanced m ell F g
  have hp:=scalar_graph_payment A C W P hW (by dsimp[P];positivity)
  have ht:h=(-A/(2*(|C|+1)))*(W/((|A|+1)*(W+P+1))):=by
    dsimp only[h,W,A,C,P,wholeStep,wholeFraction]
    congr 4; ring
  rw [←ht] at hp
  change |h*A+h^2*C|≤W/2
  calc
    _≤|h*A|+|h^2*C|:=abs_add_le _ _
    _=|h| *|A|+|h|^2*|C|:=by rw [abs_mul,abs_mul,abs_pow]
    _≤|h| *(|A|+|C|):=by
      have hh:|h|^2≤|h|:=by nlinarith[abs_nonneg h,hp.2.1]
      nlinarith only[mul_le_mul_of_nonneg_right hh (abs_nonneg C)]
    _≤|h| *P:=mul_le_mul_of_nonneg_left (by dsimp[P];linarith only[hG]) (abs_nonneg h)
    _≤W/2:=hp.2.2

/-- One actual action both descends and returns an upper price for its original starting input. -/
theorem actual_whole_electric_mean_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    let original:=∫q:ℝ,physicalMean s hs half advanced q (frequencyState half advanced m ell F g q)
    let updated:=∫q:ℝ,∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ
    updated≤original-wholeMeanDebit s hs half advanced m ell F g ∧
    original≤updated+wholeNormPrice half advanced m ell F g/2:=by
  dsimp only
  rw [(actual_whole_electric_physical_action s hs half advanced m ell F g).2.2]
  have hlam:=whole_fraction_interval s hs half advanced m ell F g
  have hd:=scalar_descent (wholeSlope s hs half advanced m ell F g) (wholeCurvature s hs half advanced m ell F g)
    (wholeFraction s hs half advanced m ell F g) hlam.1 hlam.2
  have hc:=whole_work_cap s hs half advanced m ell F g
  constructor
  · unfold wholeStep wholeMeanDebit
    have hpay:=add_le_add_left hd (∫q:ℝ,physicalMean s hs half advanced q (frequencyState half advanced m ell F g q))
    convert hpay using 1 <;> ring
  · have hl:=neg_le_of_abs_le hc
    linarith only[hl]
end LowEnergy.FirstCurrentWholeCarrier
