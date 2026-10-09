import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveJointPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentClockPrimitive
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiCombinedScalePressure
open SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceScalarEssentialBudget
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentGeometricPayer
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
open SourceClockPhiRadiusAcceleration SourceClockPhiRadiusSourceCurrent SourceScalarVirialBulk
open FirstCurrentPrimitiveNoether SourceClockAcceleration SourceClockFixedInputSeed SourceDilationRemainder
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev M : End := matchedTester
private abbrev X : End := weightedElectricCurrent
private abbrev P : End := electricPrimitive
private abbrev W : End := magneticVolumeWeight
private abbrev B : End := scalarBulkComplete
private abbrev H0 : End := diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction normalizedState normalizedForcing correctedCompleteCore updatedForcing
  weightedElectricCurrent matchedTester combinedGenerator volumeAction inverseVolumeAction dilation scalarBulkComplete geometricScalarCurrent
private theorem gauge_weight_smooth(i j:Fin 3)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun v=>volume v*gaugeWeight v i j) z.val:=
  volume_smooth.contDiffAt.mul (gaugeWeight_smooth i j z)
private theorem polynomial_smooth(i j:Fin 6):ContDiff ℝ ∞ (fun z:SourceCoordinateSlice=>
    GaussCoframeKinetic.polynomial z.1 i j):=by
  fin_cases i <;> fin_cases j <;> simp [GaussCoframeKinetic.polynomial] <;> fun_prop
private def polynomialAction(i j:Fin 6):End:=multiply
  (fun z=>GaussCoframeKinetic.polynomial z.1 i j) (fun _=>(polynomial_smooth i j).contDiffAt)
private def reflectedPair(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
    (((coordinateAction i*coordinateAction j)-polynomialAction i j)
      (SourceCoframeCovariantAction.covariantMomentum j g))
private def gaugePair(f g:QuantumTest):ℂ:=
  (1/2:ℂ)*∑a:LieIndex,∑i:Fin 3,∑j:Fin 3,
    sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
      (multiply (fun z=>volume z*gaugeWeight z i j) (gauge_weight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) g))
private def scalarPair(f g:QuantumTest):ℂ:=
  ∑a:ScalarIndex,sourcePair (U (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
    (U (GaussCoreDifferential.covariantMomentum (scalarDirection a) g))
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem physical_diagonal(half advanced:Bool)(z:ℂ)(w f:QuantumTest):
    physicalJointPrice half advanced z (w,f)=
      scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
        ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
      remainingGeometricPrice w z:=by
  have hR:(reflectedPair (U w) (U w)).re=reflectedForm (U w):=rfl
  have hG:(gaugePair (U w) (U w)).re=gaugeForm (U w):=by
    unfold gaugePair gaugeForm
    simp only[Complex.mul_re,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat]
    norm_num
  have hS:(scalarPair w w).re=inverseNativeEnergy w:=by
    unfold scalarPair inverseNativeEnergy
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _=>pair_norm _)
  unfold physicalJointPrice physicalJointKernel FirstCurrentElectricSuccessor.jointSourceKernel remainingGeometricPrice
  change (((-Complex.I*(scalarNoetherFactor half:ℂ)*(if advanced then (-1:ℂ) else 1))*
    (sourcePair f (B w)-(1/2:ℂ)*sourcePair w (geometricScalarCurrent w))+
    (3*(n:ℂ))*reflectedPair (U w) (U w)+(10:ℂ)*gaugePair (U w) (U w)+
    (magneticPrimitiveFactor:ℂ)*sourcePair w ((W*wedgeAction) w)+
    (9*(n:ℂ)/4)*Complex.I*sourcePair (U (D w)) (Dc (U w))+
    (35*(n:ℂ)/96)*sourcePair (U (D w)) (U (D w))+
    6*sourcePair (M w) (z • w)-(n/48:ℂ)*sourcePair (M w) (M w)-
    (7*(n:ℂ))*scalarPair w w)-(magneticPrimitiveFactor:ℂ)*sourcePair w ((W*wedgeAction) w)+
    4*sourcePair w (U (SourceScalarVirialBulk.magneticAction w))).re=_
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.re_ofNat,
    Complex.im_ofNat,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,hR,hG,hS,
    pair_norm (U (D w)),pair_norm (M w)]
  cases advanced <;> norm_num <;> ring

/-- The exact source gap lets complete channel producers integrate both signed prices without re-expanding their fields. -/
theorem actual_full_source_primitive_gap(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    primitiveJointPrice half advanced z w f-physicalJointPrice half advanced z (w,f)=
      magneticNoetherPrice z w f-4*(sourcePair w (U (magneticAction w))).re:=by
  have h:=(actual_full_source_primitive_noether m ell F z hz g w f he).2.1
  rw [physical_diagonal]
  unfold primitiveJointPrice remainingGeometricPrice
  rw [h]
  ring
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=by
  unfold U inverseVolumeAction
  exact multiply_pair _ _ _ _
private theorem clock_pair(f g:QuantumTest):sourcePair f (clock g)=sourcePair (clock f) g:=by rw [original_clock];exact multiply_pair _ _ _ _
private theorem self_im(T:End)(hT:∀f g,sourcePair f (T g)=sourcePair (T f) g)(w:QuantumTest):
    (sourcePair w (T w)).im=0:=by
  have h:=congrArg Complex.im (GaussNativeForm.pair_conjugate w (T w))
  rw [hT w w] at h
  simp only[Complex.conj_im] at h
  rw [hT w w]
  linarith only[h]
private theorem clock_current_pair(f g:QuantumTest):sourcePair f (clockCurrent g)=sourcePair (clockCurrent f) g:=
  SourceClockFixedInputSeed.original_clock_current_pair _ _
private theorem completed_pair_source(w:QuantumTest):
    (sourcePair w (completedAcceleration w)).re=
      2*(sourcePair (H0 w) (clockCurrent w)).im+(n/2)*(sourcePair (U w) (H0 w)).re:=by
  have hJ:=clock_current_pair w (H0 w)
  have hH:=diagonalAction_pair w (clockCurrent w)
  have hV:=U_pair w (H0 w)
  have hVH:=diagonalAction_pair w (U w)
  have hconj:=GaussNativeForm.pair_conjugate (H0 w) (clockCurrent w)
  have hconjV:=GaussNativeForm.pair_conjugate (U w) (H0 w)
  unfold completedAcceleration SourceClockAcceleration.clockAcceleration
  simp only[LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r]
  change (((-Complex.I)*(sourcePair w (H0 (clockCurrent w))-sourcePair w (clockCurrent (H0 w))))+
    ((n:ℂ)/4)*(sourcePair w (U (H0 w))+sourcePair w (H0 (U w)))).re=_
  rw [hJ,hH,hV,hVH,←hconj,←hconjV]
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re]
  norm_num
  ring
private theorem completed_full_source(w f:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w (completedAcceleration w)).re=
      2*(sourcePair f (clockCurrent w)).im-2*z.im*(sourcePair w (clockCurrent w)).re+
      (n/2)*(sourcePair (U w) f).re+(n/2)*z.re*(sourcePair w (U w)).re:=by
  rw [completed_pair_source,he]
  simp only[pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,←U_pair,
    Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,
    self_im clockCurrent clock_current_pair w,self_im U U_pair w,mul_zero,sub_zero]
  ring
private theorem clock_ward(w f:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w (clockCurrent w)).re=2*z.im*(sourcePair w (clock w)).re-2*(sourcePair f (clock w)).im:=by
  have hc:sourcePair w (bracket H0 clock w)=sourcePair (H0 w) (clock w)-sourcePair (clock w) (H0 w):=by
    simp only[bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,clock_pair]
  have hi:bracket H0 clock=(-Complex.I) • clockCurrent:=by
    unfold clockCurrent bracket
    simp only[smul_smul]
    rw [show (-Complex.I)*Complex.I=1 by rw [neg_mul,Complex.I_mul_I];ring,one_smul]
  rw [hi,LinearMap.smul_apply,pair_smul_r,he,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r] at hc
  have hp:=congrArg Complex.im hc
  have hj:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (clock w))
  have hw:sourcePair (clock w) w=sourcePair w (clock w):=(clock_pair w w).symm
  rw [hw] at hp
  simp only[Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.sub_im,Complex.add_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    self_im clock clock_pair w,mul_zero,zero_mul,neg_zero,zero_add] at hp hj
  linarith only[hp,hj]

/-- The logarithm-free restriction is generated from the same P; it is not a replacement primitive. -/
def positivePrimitive:End:=(2/(n:ℂ)) • phiSquare+(1/2:ℂ) • electricAction
private theorem positive_primitive_source:positivePrimitive=electricPrimitive+(4/(n:ℂ)) • clock:=by
  have hp:=actual_primitive_source_identity.2
  change electricPrimitive=(2/(n:ℂ)) • phiSquare+(1/2:ℂ) • electricAction-(4/(n:ℂ)) • clock at hp
  rw [hp]
  unfold positivePrimitive
  module
private theorem primitive_force(w f:QuantumTest):(sourcePair f (electricPrimitive w)).im=
    (sourcePair f (positivePrimitive w)).im-(4/n)*(sourcePair f (clock w)).im:=by
  have h:=congrArg (fun T:End=>(sourcePair f (T w)).im) positive_primitive_source
  simp only[LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r,Complex.add_im,
    show (4/(n:ℂ))=((4/n:ℝ):ℂ) by push_cast;rfl,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at h
  linarith only[h]

def clockPrimitiveForce(z:ℂ)(w f:QuantumTest):ℝ:=
  (24/n)*(sourcePair f (clockCurrent w)).im+6*(sourcePair (U w) f).re+
  12*z.im*(sourcePair f (positivePrimitive w)).im-6*z.im*(sourcePair w (coframeElectricCurrent w)).im-
  (24*z.im^2/n)*‖embed (phiRadiusAction w)‖^2-6*z.im^2*(sourcePair w (electricAction w)).re

/-- The complete source cancels logV, real frequency and their forcing terms jointly. -/
theorem actual_full_source_clock_primitive_balance(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (w f:QuantumTest)(he:H0 w=f+z • w):
    (12/n)*(sourcePair w (completedAcceleration w)).re+6*(sourcePair (M w) (z • w)).re=
      clockPrimitiveForce z w f:=by
  rw [completed_full_source w f z he,clock_ward w f z he,
    (actual_full_source_primitive_noether m ell F z hz g w f he).2.1]
  unfold primitivePhasePrice clockPrimitiveForce
  rw [primitive_force]
  field_simp[n_pos.ne']
  ring
private theorem scalar_inverse(w:QuantumTest):scalarForm (U w)=inverseNativeEnergy w:=
  original_inverse_native_return w
private theorem volume_pair(f g:QuantumTest):sourcePair f (volumeAction g)=sourcePair (volumeAction f) g:=by
  unfold volumeAction
  exact multiply_pair _ _ _ _
private theorem spatial_split:spatialAction=scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (spatialPotential z:ℂ) • f z=
    ((-(sourceTime 0*volume z/2 * ∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)):ℝ):ℂ) • f z+
      (magneticPotential z:ℂ) • f z
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
private theorem spatial_inverse(w:QuantumTest):spatialForm (U w)=
    (sourcePair w (U (scalarSpatialAction w))).re+(sourcePair w (U (magneticAction w))).re:=by
  have hc:Commute spatialAction volumeAction:=SourceHamiltonianVolume.real_volume _ _
  have h:=LinearMap.congr_fun hc.eq (U w)
  change spatialAction (volumeAction (U w))=volumeAction (spatialAction (U w)) at h
  rw [volume_inverse] at h
  unfold spatialForm
  rw [←h,←U_pair,spatial_split,LinearMap.add_apply,map_add,pair_add_r,Complex.add_re]

/-- Full comparison current after the actual H0 source has cancelled all logarithmic and real-frequency words. -/
def clockJointPrice(half advanced:Bool)(z:ℂ)(w f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+clockPrimitiveForce z w f+
  12*n*spinForm (U w)+12*n*densityForm (U w)-24*n*radiusForm w-
  12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w-
  (9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im+(35*n/96)*‖embed (U (D w))‖^2-
  (n/48)*‖embed (M w)‖^2

/-- The positive reflected/gauge/magnetic block is consumed by one original completed-current source.
The output retains the actual scalar-gauge, spin/Number and all forcing responsibilities. -/
theorem actual_full_source_clock_joint_return(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    physicalJointPrice half advanced z (w,f)=clockJointPrice half advanced z w f-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  have hC:=original_completed_reflected_form w
  rw [scalar_inverse,spatial_inverse] at hC
  have hscaled:(12/n)*(sourcePair w (completedAcceleration w)).re=
      3*n*reflectedForm (U w)+6*n*inverseNativeEnergy w+12*gaugeForm (U w)-
      12*n*spinForm (U w)-12*n*densityForm (U w)+24*n*radiusForm w+
      12*((sourcePair w (U (scalarSpatialAction w))).re+(sourcePair w (U (magneticAction w))).re):=by
    rw [hC]
    field_simp[n_pos.ne']
    ring
  have hP:=actual_full_source_clock_primitive_balance m ell F z hz g w f he
  rw [physical_diagonal]
  unfold remainingGeometricPrice clockJointPrice
  linarith only[hscaled,hP]
private theorem pair_sum_r {ι:Type*}[Fintype ι](f:QuantumTest)(v:ι→QuantumTest):
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i):=by simp only[sourcePair,map_sum,inner_sum]
private theorem gauge_volume_form(f:QuantumTest):(sourcePair f (volumeAction (gaugeKinetic f))).re=gaugeForm f:=by
  have ht(a:LieIndex)(i j:Fin 3):sourcePair (volumeAction f)
      (sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j) f)=
      sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z=>volume z*gaugeWeight z i j) (gauge_weight_smooth i j)
          (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)):=by
    change sourcePair (volumeAction f) (GaussMomentumAdjoint.adjoint (gaugeDirection i a)
      (multiply (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)))=_
    rw [GaussNativeForm.adjoint_pair]
    have hc:=LinearMap.congr_fun (SourceHamiltonianVolume.native_momentum_volume (gaugeDirection i a)).eq f
    change GaussCoreDifferential.covariantMomentum (gaugeDirection i a) (volumeAction f)=
      volumeAction (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f) at hc
    rw [hc,←volume_pair]
    congr 1
    apply DFunLike.ext
    intro z
    unfold volumeAction
    change (volume z:ℂ) • ((gaugeWeight z i j:ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z))=
      ((volume z*gaugeWeight z i j:ℝ):ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z)
    simp only[smul_smul,Complex.ofReal_mul]
  rw [volume_pair]
  simp only[gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_r,pair_sum_r,ht]
  unfold gaugeForm
  simp only[Complex.mul_re,Complex.div_re,Complex.div_im]
  norm_num
private theorem gauge_nonnegative(w:QuantumTest):0≤gaugeForm (U w):=by
  rw [←gauge_volume_form]
  rw [electric_physical_return]
  exact original_gauge_kinetic_nonnegative _
private theorem magnetic_nonnegative(w:QuantumTest):0≤(sourcePair w (U (magneticAction w))).re:=by
  have hs:inverseRootAction*inverseRootAction=U:=LinearMap.ext inverse_root_square
  have hc:Commute inverseRootAction magneticAction:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (inverseRootVolume z:ℂ) (magneticPotential z:ℂ) (f z)
  have hp:sourcePair w (U (magneticAction w))=
      sourcePair (inverseRootAction w) (magneticAction (inverseRootAction w)):=by
    rw [←hs]
    change sourcePair w (inverseRootAction (inverseRootAction (magneticAction w)))=_
    rw [show sourcePair w (inverseRootAction (inverseRootAction (magneticAction w)))=
      sourcePair (inverseRootAction w) (inverseRootAction (magneticAction w)) from multiply_pair _ _ _ _]
    exact congrArg (sourcePair (inverseRootAction w)) (LinearMap.congr_fun hc.eq w)
  rw [hp]
  exact SourceClockPhiSecondBulk.original_magnetic_nonnegative _

/-- Both remaining gauge and magnetic signs are discharged by their actual original square producers. -/
theorem actual_full_source_clock_joint_payment(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    physicalJointPrice half advanced z (w,f)≤clockJointPrice half advanced z w f:=by
  rw [actual_full_source_clock_joint_return half advanced m ell F z hz g w f he]
  linarith only[gauge_nonnegative w,magnetic_nonnegative w]
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  linarith[n_pos,actual_source_noether_gap half]
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

/-- The same generated fixed-pole source and its actual complete K clock consume the full current payment. -/
theorem actual_updated_clock_joint_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    physicalJointPrice half advanced z a≤clockJointPrice half advanced z a.1 a.2:=by
  dsimp only
  have h:=((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x
  exact actual_full_source_clock_joint_payment half advanced m ell F _ (frequency_nonreal half advanced q) g _ _ h
end LowEnergy.FirstCurrentClockPrimitive
