import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiClockPrimitiveJoint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentClockPrimitiveSquare
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
open FirstCurrentClockPrimitive

private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem phi_pair(f g:QuantumTest):sourcePair f (phiSquare g)=sourcePair (phiSquare f) g:=by
  change sourcePair f (phiRadiusAction (phiRadiusAction g))=sourcePair (phiRadiusAction (phiRadiusAction f)) g
  have hr(a b:QuantumTest):sourcePair a (phiRadiusAction b)=sourcePair (phiRadiusAction a) b:=multiply_pair _ _ _ _
  rw [hr,hr]
private theorem E_pair(f g:QuantumTest):sourcePair f (electricAction g)=sourcePair (electricAction f) g:=multiply_pair _ _ _ _
private theorem positive_pair(f g:QuantumTest):sourcePair f (positivePrimitive g)=sourcePair (positivePrimitive f) g:=by
  unfold positivePrimitive
  simp only[LinearMap.add_apply,LinearMap.smul_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,
    phi_pair,E_pair,Complex.star_def,map_div₀,map_ofNat,map_one,Complex.conj_ofReal]

def primitiveEnergy(w:QuantumTest):ℝ:=(sourcePair w (positivePrimitive w)).re

theorem actual_positive_primitive_energy(w:QuantumTest):
    primitiveEnergy w=(2/n)*‖embed (phiRadiusAction w)‖^2+(1/2:ℝ)*(sourcePair w (electricAction w)).re ∧
    0≤primitiveEnergy w:=by
  have hp:sourcePair w (phiSquare w)=sourcePair (phiRadiusAction w) (phiRadiusAction w):=multiply_pair _ _ _ _
  have he:primitiveEnergy w=(2/n)*‖embed (phiRadiusAction w)‖^2+(1/2:ℝ)*(sourcePair w (electricAction w)).re:=by
    unfold primitiveEnergy positivePrimitive
    simp only[LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r,hp,
      Complex.add_re,Complex.mul_re,Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,Complex.normSq_ofReal,Complex.one_re,Complex.one_im,pair_norm]
    field_simp[n_pos.ne']
    ring
  refine ⟨he,?_⟩
  rw [he]
  have hE:=JointElectricSource.actual_electric_energy_nonnegative w
  exact add_nonneg (mul_nonneg (div_nonneg (by norm_num) n_pos.le) (sq_nonneg _)) (mul_nonneg (by norm_num) hE)

/-- The opposite forcing belongs to the same state and full H0 equation, including every defect. -/
def oppositeForcing(z:ℂ)(w f:QuantumTest):QuantumTest:=f+(2*(z.im:ℂ)*Complex.I) • w

theorem actual_opposite_full_forcing(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    H0 w=oppositeForcing z w f+star z • w:=by
  rw [he]
  unfold oppositeForcing
  have hz:2*(z.im:ℂ)*Complex.I+star z=z:=by apply Complex.ext <;> simp; ring
  rw [add_assoc,←add_smul,hz]

private theorem source_im(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    (sourcePair f w).im=z.im*‖embed w‖^2:=by
  have hh:=diagonalAction_pair w w
  have hc:=GaussNativeForm.pair_conjugate w (H0 w)
  rw [hh] at hc
  have hi:=congrArg Complex.im hc
  simp only[Complex.conj_im] at hi
  have hf:=congrArg (fun v=>(sourcePair v w).im) he
  simp only[pair_add_l,pair_smul_l,Complex.add_im,Complex.mul_im,Complex.star_def,
    Complex.conj_im,Complex.conj_re] at hf
  have hw:(sourcePair w w).im=0:=by
    have h:=congrArg Complex.im (GaussNativeForm.pair_conjugate w w)
    simp only[Complex.conj_im] at h
    linarith only[h]
  rw [hw,pair_norm,mul_zero,zero_add] at hf
  linarith only[hi,hf]

theorem actual_opposite_forcing_norm(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    ‖embed (oppositeForcing z w f)‖^2=‖embed f‖^2:=by
  rw [←pair_norm,oppositeForcing]
  simp only[pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
  rw [←GaussNativeForm.pair_conjugate f w]
  simp only[Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.star_def,map_mul,map_ofNat,
    Complex.conj_I,Complex.conj_ofReal,Complex.conj_re,Complex.conj_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im,
    pair_norm,source_im z w f he]
  ring_nf
  simp only[Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat,pair_norm,source_im z w f he]
  ring

/-- The electric/scalar damping is an actual opposite-forcing square, not an endpoint bound. -/
theorem actual_primitive_forcing_square(z:ℂ)(w f:QuantumTest):
    12*z.im*(sourcePair f (positivePrimitive w)).im-12*z.im^2*primitiveEnergy w=
      3*primitiveEnergy f-3*primitiveEnergy (oppositeForcing z w f):=by
  have hc:sourcePair w (positivePrimitive f)=star (sourcePair f (positivePrimitive w)):=by
    rw [positive_pair]
    exact (GaussNativeForm.pair_conjugate f (positivePrimitive w)).symm
  unfold primitiveEnergy oppositeForcing
  simp only[map_add,map_smul,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,hc,
    Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.star_def,map_mul,map_ofNat,
    Complex.conj_I,Complex.conj_ofReal,Complex.conj_re,Complex.conj_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im]
  ring_nf
  simp only[Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring


private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=(-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only[smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=(1:ℂ):=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1; congr 1; ring
private theorem clock_current_return:clockCurrent=(3*(n:ℂ)/4) • (Dc*U-Complex.I • U):=by
  rw [original_clock_current]
  change (3*(n:ℂ)/8) • (U*Dc+Dc*U)=(3*(n:ℂ)/4) • (Dc*U-Complex.I • U)
  linear_combination (norm:=module) (-(3*(n:ℂ)/8)) • inverse_dilation
private theorem clock_force_return(f w:QuantumTest):
    (24/n)*(sourcePair f (clockCurrent w)).im+6*(sourcePair (U w) f).re=
      -6*(sourcePair (M w) f).re+6*(sourcePair (U (D w)) f).re:=by
  rw [clock_current_return]
  simp only[M,matchedTester,matchedColumn,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,pair_add_l,pair_sub_r,pair_smul_l,pair_smul_r]
  rw [←GaussNativeForm.pair_conjugate f (U w),←GaussNativeForm.pair_conjugate f (Dc (U w))]
  simp only[Complex.star_def,map_mul,map_ofNat,Complex.conj_I,
    Complex.add_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,
    Complex.normSq_ofNat,Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im]
  field_simp[n_pos.ne']
  ring

def oppositePrimitiveDebit(w:QuantumTest):ℝ:=3*primitiveEnergy w-(432/n)*‖embed w‖^2

def completeSourceRemainder(half advanced:Bool)(z:ℂ)(w f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
  6*(sourcePair (U (D w)) f).re+3*primitiveEnergy f-
  6*z.im*(sourcePair w (coframeElectricCurrent w)).im+
  12*n*spinForm (U w)+12*n*densityForm (U w)-24*n*radiusForm w-
  12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w-
  (9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im+(35*n/96)*‖embed (U (D w))‖^2

/-- Both genuine full forcing legs stay in one signed budget. The negative matched square,
original gauge and magnetic prices are retained, and the bare forcing norm is eliminated internally. -/
theorem actual_full_source_two_pole_joint_balance(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    physicalJointPrice half advanced z (w,f)=completeSourceRemainder half advanced z w f-
      oppositePrimitiveDebit (oppositeForcing z w f)-
      (n/48)*‖embed (M w)+((144/n:ℝ):ℂ) • embed f‖^2-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  have hp:=actual_primitive_forcing_square z w f
  have hs : -6*(sourcePair (M w) f).re-(n/48)*‖embed (M w)‖^2=
      (432/n)*‖embed f‖^2-(n/48)*‖embed (M w)+((144/n:ℝ):ℂ) • embed f‖^2:=by
    simpa only[sourcePair] using FiniteCausalSylvester.noether_clock_square n n_pos (embed (M w)) (embed f)
  have hn:=actual_opposite_forcing_norm z w f he
  have hE:12*z.im^2*primitiveEnergy w=
      (24*z.im^2/n)*‖embed (phiRadiusAction w)‖^2+6*z.im^2*(sourcePair w (electricAction w)).re:=by
    rw [(actual_positive_primitive_energy w).1]
    ring
  rw [actual_full_source_clock_joint_return half advanced m ell F z hz g w f he]
  unfold clockJointPrice clockPrimitiveForce completeSourceRemainder oppositePrimitiveDebit
  rw [hn]
  have hf:=clock_force_return f w
  linarith only[hp,hs,hE,hf]

/-- The generated source update consumes the same two-pole balance at every actual Gaussian clock. -/
theorem actual_updated_two_pole_joint_balance(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    physicalJointPrice half advanced z a=completeSourceRemainder half advanced z a.1 a.2-
      oppositePrimitiveDebit (oppositeForcing z a.1 a.2)-
      (n/48)*‖embed (M a.1)+((144/n:ℝ):ℂ) • embed a.2‖^2-
      2*gaugeForm (U a.1)-8*(sourcePair a.1 (U (magneticAction a.1))).re:=by
  dsimp only
  have h:=((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x
  have hn:0<sourceNoetherFrequency half:=by linarith[n_pos,actual_source_noether_gap half]
  have hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
    cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
      Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hn.ne'
  exact actual_full_source_two_pole_joint_balance half advanced m ell F _ hz g _ _ h
end LowEnergy.FirstCurrentClockPrimitiveSquare
