import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeDensitySource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudgetNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussCoframeForm GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceCoframeCovariantAction SourceCoframeCovariantSquare SourceClockReflectedForm
open SourceDilationRemainder SourceScalarVirialBulk SourceHamiltonianVolume
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget SourceScalarInverseNativeEnergy
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentJointBudget FirstCurrentPayerNext NativePointReturn
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev V : End := volumeAction
private abbrev Hc : End := covariantKinetic
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev M : End := matchedTester
attribute [local irreducible] sourcePair embed diagonalAction covariantKinetic dilation matchedTester
private theorem pair_add_right(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_smul_right(f g:QuantumTest)(c:ℂ):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_right {ι:Type*}[Fintype ι](f:QuantumTest)(q:ι→QuantumTest):
    sourcePair f (∑i,q i)=∑i,sourcePair f (q i):=by simp only[sourcePair,map_sum,inner_sum]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by simpa only[sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem volume_pair(f g:QuantumTest):sourcePair f (V g)=sourcePair (V f) g:=multiply_pair _ _ _ _
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _
private theorem gauge_volume_smooth(i j:Fin 3)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun w=>volume w*gaugeWeight w i j) z.val:=
  volume_smooth.contDiffAt.mul (gaugeWeight_smooth i j z)
private theorem gauge_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (gaugeKinetic f))).re=gaugeForm f := by
  have ht (a : LieIndex) (i j : Fin 3) : sourcePair (volumeAction f)
      (sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) f)=
      sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => volume z*gaugeWeight z i j) (gauge_volume_smooth i j)
          (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)) := by
    change sourcePair (volumeAction f) (GaussMomentumAdjoint.adjoint (gaugeDirection i a)
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)))=_
    rw [GaussNativeForm.adjoint_pair]
    have hc := LinearMap.congr_fun (SourceHamiltonianVolume.native_momentum_volume (gaugeDirection i a)).eq f
    change GaussCoreDifferential.covariantMomentum (gaugeDirection i a) (volumeAction f)=
      volumeAction (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f) at hc
    rw [hc,←volume_pair]
    congr 1
    apply DFunLike.ext
    intro z
    change (volume z:ℂ) • ((gaugeWeight z i j:ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z))=
      ((volume z*gaugeWeight z i j:ℝ):ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z)
    simp only [smul_smul,Complex.ofReal_mul]
  rw [volume_pair]
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_right,pair_sum_right,ht]
  unfold gaugeForm
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im]
  norm_num

private theorem spin_volume_action (a : Fin 7) :
    volumeAction*(GaussCoframeSpin.current a*multiply inverseVolume inverseVolume_smooth*GaussCoframeSpin.current a)=
      (sourceTime 0:ℂ) • (GaussCoframeSpin.current a*GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
      ((inverseVolume z:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z))))=
      (sourceTime 0:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
        (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z)))
    rw [map_smul,smul_smul]
    congr 1
    unfold inverseVolume
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem spin_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (spinRemainder f))).re=sourceTime 0*spinForm f := by
  have he : volumeAction*spinRemainder=
      ∑ a : Fin 7,((residualWeight a:ℂ)*(sourceTime 0:ℂ)) • (GaussCoframeSpin.current a*GaussCoframeSpin.current a) := by
    unfold spinRemainder
    simp only [Finset.mul_sum,mul_smul_comm,spin_volume_action,smul_smul]
  have hs (a : Fin 7) : sourcePair f (GaussCoframeSpin.current a (GaussCoframeSpin.current a f))=
      sourcePair (GaussCoframeSpin.current a f) (GaussCoframeSpin.current a f) := GaussCoframeSpin.current_pair a f _
  change (sourcePair f ((volumeAction*spinRemainder) f)).re=_
  rw [he]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_sum_right,pair_smul_right,
    hs,Complex.re_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,pair_norm,spinForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem number_volume_action : volumeAction*numberShift=
    ((-9*(sourceTime 0:ℂ)/8):ℂ) • number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · apply PiLp.ext
    intro word
    change (volume z:ℂ)*((1/2:ℂ)*
      ((number (multiply numberCoefficient numberCoefficient_smooth f) z word)+
      (numberCoefficient z:ℂ)*(number f z word)))=(-9*(sourceTime 0:ℂ)/8)*(number f z word)
    rw [number_apply,number_apply]
    change (volume z:ℂ)*((1/2:ℂ)*((word.card:ℂ)*((numberCoefficient z:ℂ)*f z word)+
      (numberCoefficient z:ℂ)*((word.card:ℂ)*f z word)))=_
    unfold numberCoefficient inverseVolume
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem number_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (numberShift f))).re= -(9*sourceTime 0/8)*numberForm f := by
  change (sourcePair f ((volumeAction*numberShift) f)).re=_
  rw [number_volume_action,LinearMap.smul_apply,pair_smul_right]
  have hc : (-9*(sourceTime 0:ℂ)/8)=((-9*sourceTime 0/8:ℝ):ℂ) := by push_cast;rfl
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,numberForm]
  ring

private theorem density_shift_form (f : QuantumTest) :
    (sourcePair f (densityShift f)).re=numberForm f+4*‖embed f‖^2 := by
  change (sourcePair f (number f+(4:ℂ) • f)).re=_
  rw [pair_add_right,pair_smul_right]
  simp only [Complex.add_re,Complex.mul_re,numberForm]
  norm_num
  rw [pair_norm]
private theorem density_shift_norm (f : QuantumTest) :
    ‖embed (densityShift f)‖^2=‖embed (number f)‖^2+8*numberForm f+16*‖embed f‖^2 := by
  change ‖embed (number f+(4:ℂ) • f)‖^2=_
  rw [map_add,map_smul,norm_add_sq (𝕜 := ℂ),norm_smul,inner_smul_right]
  have hc : ‖(4:ℂ)‖=4 := by norm_num
  rw [hc]
  have hn:(inner ℂ (embed (number f)) (embed f)).re=numberForm f:=by
    simpa only[sourcePair,numberForm] using congrArg Complex.re (number_pair f f).symm
  simp only[RCLike.re_eq_complex_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,hn]
  ring

private theorem relative_form(A:End)(hA:∀f g:QuantumTest,sourcePair f (A g)=sourcePair (A f) g)(w:QuantumTest):
    (sourcePair w (U (A w))).re=(sourcePair (U w) (V (A (U w)))).re:=by
  rw [volume_pair,volume_inverse,U_pair,hA w (U w)]
  simpa only [Complex.conj_re] using congrArg Complex.re (pair_conjugate (U w) (A w))
private theorem spin_pair(f g:QuantumTest):sourcePair f (spinRemainder g)=sourcePair (spinRemainder f) g:=by
  simp only[spinRemainder,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_sum,map_smul,inner_sum,sum_inner,inner_smul_right,inner_smul_left,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have h:sourcePair f (GaussCoframeSpin.current a (multiply inverseVolume inverseVolume_smooth (GaussCoframeSpin.current a g)))=
      sourcePair (GaussCoframeSpin.current a (multiply inverseVolume inverseVolume_smooth (GaussCoframeSpin.current a f))) g:=
    (GaussCoframeSpin.current_pair a f _).trans
      ((multiply_pair _ _ _ _).trans (GaussCoframeSpin.current_pair a _ g))
  simpa only[sourcePair] using h
private theorem number_shift_pair(f g:QuantumTest):sourcePair f (numberShift g)=sourcePair (numberShift f) g:=by
  let L:End:=multiply numberCoefficient numberCoefficient_smooth
  have h1:sourcePair f (number (L g))=sourcePair (L (number f)) g:=
    (number_pair f (L g)).trans (multiply_pair _ _ _ _)
  have h2:sourcePair f (L (number g))=sourcePair (number (L f)) g:=
    (multiply_pair _ _ _ _).trans (number_pair (L f) g)
  change sourcePair f ((1/2:ℂ) • (number (L g)+L (number g)))=
    sourcePair ((1/2:ℂ) • (number (L f)+L (number f))) g
  have hr:star (1/2:ℂ)=(1/2:ℂ):=by norm_num
  simp only[sourcePair,map_smul,map_add,inner_smul_right,inner_smul_left,inner_add_right,inner_add_left,starRingEnd_apply,hr] at h1 h2 ⊢
  rw [h1,h2]
  ring
private theorem spatial_split:spatialAction=scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (spatialPotential z:ℂ) • f z=((-(sourceTime 0*volume z/2 * ∑ i:Fin 3,∑ j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)):ℝ):ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
private def localVolume : End := multiply volumePotential volumePotential_smooth
private theorem local_volume_return(w:QuantumTest):U (localVolume w)=(3*(n:ℂ)) • w:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volumePotential z:ℂ) • w z)=(3*(n:ℂ)) • w z
    rw [smul_smul]
    congr 1
    unfold reciprocalVolume volumePotential
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne']
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

def nativeDensityPrice(w:QuantumTest):ℝ:=n*((27/4:ℝ)*‖embed (number (U w))‖^2+
  (99/2:ℝ)*numberForm (U w)+90*‖embed (U w)‖^2)

/-- Spin and scalar spatial sectors cancel in the original native/local-plus-field word.
Its remaining Number/density polynomial is retained for the same coframe current. -/
theorem actual_remaining_field_density_source(w:QuantumTest):
    remainingNativeField w=10*gaugeForm (U w)+4*(sourcePair w (U (magneticAction w))).re+
      nativeDensityPrice w+72*n*‖embed w‖^2:=by
  have hG:=relative_form gaugeKinetic gaugeKinetic_pair w
  rw [gauge_volume_form] at hG
  have hS:=relative_form spinRemainder spin_pair w
  rw [spin_volume_form] at hS
  have hN:=relative_form numberShift number_shift_pair w
  rw [number_volume_form] at hN
  have hP:=relative_form spatialAction (fun f g=>multiply_pair _ _ f g) w
  change (sourcePair w (U (spatialAction w))).re=spatialForm (U w) at hP
  rw [spatial_split,LinearMap.add_apply,map_add,pair_add_right,Complex.add_re] at hP
  have hL:(sourcePair w (U (localVolume w))).re=3*n*‖embed w‖^2:=by
    rw [local_volume_return,pair_smul_right]
    simp only[Complex.mul_re,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,pair_norm]
  change ((22:ℂ)*sourcePair w (U (gaugeKinetic w))+(12:ℂ)*sourcePair w (U (scalarSpatialAction w))+
    (16:ℂ)*sourcePair w (U (magneticAction w))+((-12:ℂ)*sourcePair w (U (spinRemainder w))+
      (-12:ℂ)*sourcePair w (U (numberShift w))+(24:ℂ)*sourcePair w (U (localVolume w)))).re+
    12*n*spinForm (U w)+12*n*densityForm (U w)-12*gaugeForm (U w)-12*spatialForm (U w)=_
  simp only[Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    Complex.neg_re,Complex.neg_im,zero_mul,sub_zero]
  rw [hG,hS,hN,hL]
  unfold densityForm nativeDensityPrice
  linear_combination (norm:=ring) 12*hP

/-- The Number-weighted source adjoint pays exactly the remaining native density polynomial. -/
theorem actual_coframe_native_density_cancellation(w:QuantumTest):
    -6*(sourcePair (M w) (Hc w)).re+nativeDensityPrice w=
      3*n*reflectedForm (U w)-(9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im:=by
  have hR:=original_reflected_covariant_form (U w)
  have hH:=relative_form Hc actual_covariant_kinetic_pair w
  rw [←hH] at hR
  have hN:=density_shift_norm (U w)
  have hD:=density_shift_form (U w)
  have hn:n≠0:=by
    rw [show n=sourceTime 0 from rfl,source_time_generated]
    exact ne_of_gt SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have he: -12*(sourcePair w (U (Hc w))).re+(27*n/4)*‖embed (Dc (U w))‖^2+
      nativeDensityPrice w=3*n*reflectedForm (U w):=by
    apply mul_left_cancel₀ hn
    unfold nativeDensityPrice
    linear_combination (norm:=ring) 12*hR-(27*n^2/4)*hN+(9*n^2/2)*hD
  have hc:=actual_coframe_matched_pair w
  linarith only[he,hc]

/-- The complete remaining native, field and covariant coframe source loses all spin and Number prices jointly. -/
theorem actual_remaining_field_coframe_payment(w:QuantumTest):
    remainingNativeField w-6*(sourcePair (M w) (Hc w)).re=
      3*n*reflectedForm (U w)+10*gaugeForm (U w)+4*(sourcePair w (U (magneticAction w))).re+
      72*n*‖embed w‖^2-(9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im:=by
  have hN:=actual_remaining_field_density_source w
  have hC:=actual_coframe_native_density_cancellation w
  linarith only[hN,hC]

/-- All lower-order density has already been consumed in this same-state physical price. -/
def densityFreeRemainder(u:QuantumTest)(z:ℂ):ℝ:=
  3*n*reflectedForm (U u)+10*gaugeForm (U u)+4*(sourcePair u (U (magneticAction u))).re+
    72*n*‖embed u‖^2-(9*n/4)*(sourcePair (U (D u)) (Dc (U u))).im+
    (35*n/96)*‖embed (U (D u))‖^2+6*(sourcePair (M u) (z • u)).re-
    (n/48)*‖embed (M u)‖^2-10*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u

/-- The complete coframe forcing square is consumed before estimation, including its actual complex frequency. -/
theorem actual_density_free_remainder(u:QuantumTest)(z:ℂ):
    correctedScalarAbsorbedRemainder u z=densityFreeRemainder u z:=by
  have hn:0<n:=by
    rw [show n=sourceTime 0 from rfl,source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hF:=FiniteCausalSylvester.noether_clock_square n hn (embed (M u)) (embed (Hc u-z • u))
  have hN:=actual_remaining_field_coframe_payment u
  simp only[map_sub,inner_sub_right,Complex.sub_re] at hF
  unfold correctedScalarAbsorbedRemainder densityFreeRemainder
  simp only[sourcePair,map_sub] at hN ⊢
  linear_combination (norm:=ring) -hF+hN

open SourceLocalizedInverseFormPayment SourceResolventBandLimit MeasureTheory Filter
private theorem frequency_nonreal(half advanced:Bool)(x:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0:=by
  have hn:0<n:=by
    rw [show n=sourceTime 0 from rfl,source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp:0<sourceNoetherFrequency half:=by linarith[actual_source_noether_gap half]
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

/-- The actual R common-payment mouth now consumes the fully cancelled native/coframe density word. -/
theorem actual_corrected_R_density_payment(half:Bool)(g:diagonal.domain):
    ∀ ε:ℝ,0<ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,∀ s:ℝ,∀ hs:0<s,
      s ≤ scalarClockWindow half → ∀ ξ η:ℝ,
      (∫⁻x:ℝ,ENNReal.ofReal (
        let z:=actualFrequency advanced (sourceNoetherFrequency half) x
        let hz:=frequency_nonreal half advanced x
        let u:=correctedCompleteCore s hs ξ η (normalizedState m ell F z hz g)
        updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
          (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
            densityFreeRemainder u z))) ≤ ENNReal.ofReal ε:=by
  simpa only[correctedScalarAbsorptionGap,actual_density_free_remainder] using
    actual_corrected_R_scalar_noether_payment half g
end LowEnergy.FirstCurrentJointBudgetNext
