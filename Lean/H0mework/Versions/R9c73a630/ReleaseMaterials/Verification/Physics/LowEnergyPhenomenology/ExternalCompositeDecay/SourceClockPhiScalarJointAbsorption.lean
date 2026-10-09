import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarForceSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentScalarForceAbsorption
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceScalarVirialBulk SourceScalarEssentialBudget
open SourceClockPhiRadiusSourceCurrent ScalarInputJointNoether FirstCurrentJointBudget ReverseNativeClock
open ReverseBalancedForcePayer ReverseScalarGaugeWard ScalarBalancedPrimitive BalancedPrimitivePayer PrimitiveInputPayer
open FirstCurrentJointForceLoss FirstCurrentClockPrimitiveSquare FirstCurrentClockPrimitive
open MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
attribute [local irreducible] sourcePair embed diagonalAction sourceTime scalarNativeSourceBlock balancedCompressionForce
  jointForceInputLoss scalarNativeLoss balancedScalarSquare
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem inverse_nonnegative(w:QuantumTest):0 ≤ inverseNativeEnergy w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem inverse_radius_pair(f g:QuantumTest):sourcePair (S f) (r g)=sourcePair f g:=by
  have he:r (S f)=f:=by
    apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  have hr:sourcePair (S f) (r g)=sourcePair (r (S f)) g:=multiply_pair _ _ _ _
  exact hr.trans (congrArg (fun v:QuantumTest=>sourcePair v g) he)
private theorem pair_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re:=by
  have h:=congrArg Complex.re (GaussNativeForm.pair_conjugate f g)
  simpa only [Complex.conj_re] using h

def shiftedDifferenceLoss(F:GaussUnitaryHistory.Index)(a:ℝ)(d w:QuantumTest):ℝ:=
  jointForceInputLoss F a (d+(3/2:ℂ) • w) w

private theorem joint_square_shift(a:ℝ)(y b c:H):
    (2/(21*n))*‖y+((14*n*a:ℝ):ℂ) • (b+(3/2:ℂ) • c)‖^2=
      (2/(21*n))*‖y+((14*n*a:ℝ):ℂ) • b‖^2+4*a*(inner ℂ c y).re+
        56*n*a^2*(inner ℂ c b).re+42*n*a^2*‖c‖^2:=by
  have he:y+((14*n*a:ℝ):ℂ) • (b+(3/2:ℂ) • c)=
      (y+((14*n*a:ℝ):ℂ) • b)+((21*n*a:ℝ):ℂ) • c:=by
    simp only [smul_add,smul_smul]
    push_cast
    module
  rw [he,norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right,
    inner_add_left,inner_smul_left,Complex.conj_ofReal,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    RCLike.re_eq_complex_re,Complex.add_re]
  have hreal(p q:H):(inner ℂ p q).re=(inner ℂ q p).re:=by
    simpa only [RCLike.re_eq_complex_re] using inner_re_symm (𝕜:=ℂ) p q
  rw [hreal y c,hreal b c]
  field_simp [n_pos.ne']
  ring

/-- The force is absorbed by shifting the same difference input, preserving the electric force energy and all ordered cross terms. -/
theorem actual_difference_force_shift(F:GaussUnitaryHistory.Index)(a:ℝ)(d w:QuantumTest):
    shiftedDifferenceLoss F a d w=jointForceInputLoss F a d w+
      4*a*(sourcePair (U w) (balancedCompressionForce F w)).re+
      56*n*a^2*(sourcePair (S (U w)) (S (U d))).re+42*n*a^2*‖embed (S (U w))‖^2:=by
  have h:=joint_square_shift a (embed (r (balancedCompressionForce F w))) (embed (S (U d))) (embed (S (U w)))
  have hp:inner ℂ (embed (S (U w))) (embed (r (balancedCompressionForce F w)))=
      sourcePair (U w) (balancedCompressionForce F w):=by
    simpa only [sourcePair] using inverse_radius_pair (U w) (balancedCompressionForce F w)
  rw [hp] at h
  unfold shiftedDifferenceLoss jointForceInputLoss
  simp only [map_add,map_smul]
  unfold sourcePair
  unfold sourcePair at h
  linear_combination h

/-- The added inverse-radius square is paid internally by the native kinetic reserve at the actual source frequency. -/
theorem actual_shifted_force_hardy_payment(half:Bool)(w:QuantumTest):
    42*n*(reverseNoetherFactor half)^2*‖embed (S (U w))‖^2≤
      6*reverseNoetherFactor half*n*inverseNativeEnergy w:=by
  let a:=reverseNoetherFactor half
  have ha:0<a ∧ a<3:=actual_source_reverse_factor_bound half
  have hI:=inverse_nonnegative w
  have hC:=actual_affine_hardy_source_cost
  have hc:42*a^2*(16*affineHardyCost/59^2)≤6*a:=by
    have ha2:a^2≤3*a:=by nlinarith only [ha.1,ha.2]
    calc
      _≤(6720/3481:ℝ)*a^2:=by nlinarith only [mul_le_mul_of_nonneg_right hC (sq_nonneg a)]
      _≤(20160/3481:ℝ)*a:=by nlinarith only [ha2]
      _≤6*a:=by nlinarith only [ha.1]
  have h:=mul_le_mul_of_nonneg_left (actual_affine_inverse_native_hardy w)
    (show 0 ≤ 42*n*a^2 by have hn:=n_pos;positivity)
  have hn:=mul_le_mul_of_nonneg_right hc (mul_nonneg n_pos.le hI)
  dsimp only [a] at h hn
  nlinarith only [h,hn]

private def vacuumSquareWeight(a:ℝ)(z:SourceCoordinateSlice):ℝ:=
  ‖scalarField z-((26/25:ℝ)+(28/5)*a) • vacuum‖^2
private theorem vacuum_square_smooth(a:ℝ):ContDiff ℝ ∞ (vacuumSquareWeight a):=
  ((scalarField_smooth.sub contDiff_const).norm_sq ℝ)
private def vacuumSquareAction(a:ℝ):End:=multiply (vacuumSquareWeight a) (fun _=>(vacuum_square_smooth a).contDiffAt)

def scalarVacuumNormPrice(a:ℝ):ℝ:=n*(336*a^2+(624/5)*a)*‖vacuum‖^2
private theorem vacuum_square_source(a:ℝ):
    ((120*a:ℝ):ℂ) • (U*vacuumLinearAction)=((75*n/7:ℝ):ℂ) • balancedScalarSquare-
      ((75*n/7:ℝ):ℂ) • vacuumSquareAction a+(scalarVacuumNormPrice a:ℂ) • (1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have hp:120*a*(reciprocalVolume z*(n*volume z*inner ℝ vacuum (scalarField z)))=
        (75*n/7)*‖scalarField z-(26/25:ℝ) • vacuum‖^2-
        (75*n/7)*vacuumSquareWeight a z+scalarVacuumNormPrice a:=by
      unfold vacuumSquareWeight scalarVacuumNormPrice
      rw [norm_sub_sq_real,norm_sub_sq_real,real_inner_smul_right,real_inner_smul_right,
        norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs,
        real_inner_comm (scalarField z) vacuum]
      unfold reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne']
      ring
    unfold balancedScalarSquare vacuumSquareAction
    change ((120*a:ℝ):ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z))=
      ((75*n/7:ℝ):ℂ) • (((‖scalarField z-(26/25:ℝ) • vacuum‖^2:ℝ):ℂ) • f z)-
      ((75*n/7:ℝ):ℂ) • ((vacuumSquareWeight a z:ℂ) • f z)+(scalarVacuumNormPrice a:ℂ) • f z
    simp only [smul_smul,←Complex.ofReal_mul,←sub_smul,←add_smul]
    simpa only [Complex.ofReal_add,Complex.ofReal_sub] using congrArg (fun c:ℝ=>(c:ℂ) • f z) hp
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem vacuum_square_nonnegative(a:ℝ)(w:QuantumTest):0 ≤ (sourcePair w (vacuumSquareAction a w)).re:=by
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫z,densityPair w (vacuumSquareAction a w) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable w (vacuumSquareAction a w))]
  apply integral_nonneg;intro z
  change 0 ≤ (densityPair w (vacuumSquareAction a w) z).re
  have he:densityPair w (vacuumSquareAction a w) z=(vacuumSquareWeight a z:ℂ)*densityPair w w z:=inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hp:0 ≤ (densityPair w w z).re:=by
    by_cases hz:z∈physicalChart
    · change 0 ≤ RCLike.re (inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (w z)) (w z))
      rw [GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
        (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    · have hw:w z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (w.tsupport_subset h))
      simp only [densityPair,hw,map_zero,inner_zero_left,Complex.zero_re,le_refl]
  exact mul_nonneg (sq_nonneg _) hp

/-- Half of the original shifted scalar loss absorbs the complete source vacuum-linear term. -/
theorem actual_scalar_vacuum_payment(a:ℝ)(w:QuantumTest):
    120*a*(sourcePair w (U (vacuumLinearAction w))).re≤
      (1/2:ℝ)*scalarNativeLoss w+scalarVacuumNormPrice a*‖embed w‖^2:=by
  have h:=congrArg (fun T:End=>(sourcePair w (T w)).re) (vacuum_square_source a)
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,Module.End.one_apply,
    pair_add_r,pair_sub_r,pair_smul_r,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,pair_norm] at h
  have hn:=mul_nonneg (show 0 ≤ 75*n/7 by have hn:=n_pos;positivity) (vacuum_square_nonnegative a w)
  have hc:0 ≤ (144*n/175)*‖vacuum‖^2*‖embed w‖^2:=by have hn:=n_pos;positivity
  unfold scalarNativeLoss
  linarith only [h,hn,hc]

def scalarForceRemainder(half:Bool)(F:GaussUnitaryHistory.Index)(d w:QuantumTest):ℝ:=
  let a:=reverseNoetherFactor half
  4*a*(sourcePair (U w) (balancedOwnDefect F w)).re-
    96*a*(sourcePair w (U (matterAction w))).re-288*a*(sourcePair w (U (magneticAction w))).re-
    168*a*(sourcePair w (U (scalarSpatialAction w))).re+
    56*n*a^2*(sourcePair (S (U w)) (S (U d))).re+
    (((scalarNoetherFactor half*n^2-102*a*n)*‖vacuum‖^2-(72+432*a)*n)+scalarVacuumNormPrice a)*‖embed w‖^2

/-- Positive scalar growth is absorbed into the same shifted force-input square, half the scalar loss and a native kinetic debit. All own-Q, matter, magnetic, spatial and signed input interference remain explicit. -/
theorem actual_scalar_force_joint_absorption(half:Bool)(F:GaussUnitaryHistory.Index)(d w:QuantumTest):
    scalarNativeSourceBlock half w+shiftedDifferenceLoss F (reverseNoetherFactor half) d w+
      (18*reverseNoetherFactor half+106/7)*n*inverseNativeEnergy w≤
      jointForceInputLoss F (reverseNoetherFactor half) d w+(1/2:ℝ)*scalarNativeLoss w+
        scalarForceRemainder half F d w:=by
  have hs:=actual_scalar_native_force_source half F w
  have hd:=actual_difference_force_shift F (reverseNoetherFactor half) d w
  have hh:=actual_shifted_force_hardy_payment half w
  have hv:=actual_scalar_vacuum_payment (reverseNoetherFactor half) w
  unfold scalarForceRemainder
  dsimp only at hs ⊢
  linear_combination (norm:=(ring_nf;norm_num)) hs+hd+hh+hv
end LowEnergy.FirstCurrentScalarForceAbsorption
