import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPhysicalForcePayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.BalancedPrimitivePayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarVirialBulk
open MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private def shiftedScalar(z:SourceCoordinateSlice):Scalar:=scalarField z-(26/25:ℝ) • vacuum
private theorem shifted_smooth:ContDiff ℝ ∞ shiftedScalar:=scalarField_smooth.sub contDiff_const

def balancedScalarSquare:End:=multiply (fun z=>‖shiftedScalar z‖^2) (fun _=>(shifted_smooth.norm_sq ℝ).contDiffAt)
private def radiusWord:End:=multiply (fun z=>4*(GaussYukawaCoefficient.radius z)^2-1)
  (fun _=>((contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const).contDiffAt)
private theorem scalar_identity(z:SourceCoordinateSlice):
    (18/7:ℝ)*‖scalarField z‖^2-(24/7:ℝ)*inner ℝ vacuum (scalarField z)-
      24*(4*(GaussYukawaCoefficient.radius z)^2-1)=
      -(150/7:ℝ)*‖shiftedScalar z‖^2-(144/175:ℝ)*‖vacuum‖^2-72:=by
  have hr:(GaussYukawaCoefficient.radius z)^2=1+‖(z.2.1:Scalar)‖^2/4:=by
    exact Real.sq_sqrt (by positivity)
  have hs:(z.2.1:Scalar)=scalarField z-vacuum:=by unfold scalarField;abel
  rw [hr,hs,norm_sub_sq_real]
  unfold shiftedScalar
  rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num:(0:ℝ)<26/25)]
  rw [real_inner_comm vacuum (scalarField z)]
  ring
private theorem scalar_operator:
    (18/7:ℂ) • (U*centeredAction)-(24/7:ℂ) • (U*vacuumLinearAction)-(24*(n:ℂ)) • radiusWord=
      (-(150*n/7:ℝ):ℂ) • balancedScalarSquare-
        (((144*n/175:ℝ)*‖vacuum‖^2+72*n:ℝ):ℂ) • (1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have hv:GaussNativeEnergy.volume z≠0:=(volume_pos ⟨z,hz⟩).ne'
    have hC:reciprocalVolume z*(n*volume z*‖scalarField z‖^2)=n*‖scalarField z‖^2:=by
      unfold reciprocalVolume
      field_simp [hv]
    have hV:reciprocalVolume z*(n*volume z*inner ℝ vacuum (scalarField z))=n*inner ℝ vacuum (scalarField z):=by
      unfold reciprocalVolume
      field_simp [hv]
    change (18/7:ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*‖scalarField z‖^2:ℝ):ℂ) • f z))-
      (24/7:ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z))-
      (24*(n:ℂ)) • (((4*(GaussYukawaCoefficient.radius z)^2-1:ℝ):ℂ) • f z)=
      (-(150*n/7:ℝ):ℂ) • (((‖shiftedScalar z‖^2:ℝ):ℂ) • f z)-
        (((144*n/175:ℝ)*‖vacuum‖^2+72*n:ℝ):ℂ) • f z
    simp only [smul_smul,←Complex.ofReal_mul,hC,hV,←sub_smul]
    congr 1
    have h:=congrArg (fun r:ℝ=>n*r) (scalar_identity z)
    have hreal:(18/7:ℝ)*(n*‖scalarField z‖^2)-(24/7:ℝ)*(n*inner ℝ vacuum (scalarField z))-
        24*n*(4*GaussYukawaCoefficient.radius z^2-1)=
      -(150*n/7)*‖shiftedScalar z‖^2-((144*n/175)*‖vacuum‖^2+72*n):=by
      linear_combination (norm:=ring) h
    have hc:=congrArg (fun r:ℝ=>(r:ℂ)) hreal
    push_cast at hc ⊢
    exact hc

  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem multiplier_nonnegative(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hs:∀z:physicalChart,0 ≤ c z.val)(w:QuantumTest):0 ≤ (sourcePair w (multiply c hc w)).re:=by
  rw [sourcePair_integral]
  have hr:(∫z,densityPair w (multiply c hc w) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair w (multiply c hc w) z).re ∂GaussHistoryHilbert.configurationMeasure:=by
    simpa only using! (integral_re (densityPair_integrable w (multiply c hc w))).symm
  rw [hr]
  apply integral_nonneg;intro z
  change 0 ≤ (densityPair w (multiply c hc w) z).re
  have he:densityPair w (multiply c hc w) z=(c z:ℂ)*densityPair w w z:=inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz:z∈physicalChart
  · have hp:0 ≤ (densityPair w w z).re:=by
      change 0 ≤ (inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (w z)) (w z)).re
      have hh:=GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
        (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le) (w z)
      simpa only [RCLike.re_eq_complex_re] using (sq_nonneg ‖GaussBoundedMultiplier.halfWeight (fun N=>GaussDensityCore.density N z) (w z)‖).trans_eq hh.symm
    exact mul_nonneg (hs ⟨z,hz⟩) hp
  · have hw:w z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (w.tsupport_subset h))
    simp only [densityPair,hw,map_zero,inner_zero_left,Complex.zero_re,mul_zero]
    exact le_refl _

theorem actual_balanced_scalar_square_nonnegative(w:QuantumTest):
    0 ≤ (sourcePair w (balancedScalarSquare w)).re:=multiplier_nonnegative _ _ (fun _=>sq_nonneg _) w

/-- The scalar potential released by the actual double primitive current is a negative source square, retaining the original vacuum offset and original Yukawa radius. -/
theorem actual_balanced_scalar_potential_payment(w:QuantumTest):
    (18/7:ℝ)*(sourcePair w (U (centeredAction w))).re-(24/7:ℝ)*(sourcePair w (U (vacuumLinearAction w))).re-
      24*n*radiusForm w=
      -(150*n/7)*(sourcePair w (balancedScalarSquare w)).re-
        ((144*n/175)*‖vacuum‖^2+72*n)*‖embed w‖^2 ∧
    (18/7:ℝ)*(sourcePair w (U (centeredAction w))).re-(24/7:ℝ)*(sourcePair w (U (vacuumLinearAction w))).re-
      24*n*radiusForm w ≤ -72*n*‖embed w‖^2:=by
  have h:=congrArg (fun T:End=>(sourcePair w (T w)).re) scalar_operator
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,Module.End.one_apply,pair_sub_r,pair_smul_r] at h
  norm_num only [Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,
    mul_zero,zero_mul,sub_zero,add_zero,zero_sub,neg_zero,pair_norm] at h
  change (18/7:ℝ)*(sourcePair w (U (centeredAction w))).re-(24/7:ℝ)*(sourcePair w (U (vacuumLinearAction w))).re-
      24*n*radiusForm w= -(150*n/7)*(sourcePair w (balancedScalarSquare w)).re-
        ((144*n/175)*‖vacuum‖^2+72*n)*‖embed w‖^2 at h
  refine ⟨h,?_⟩
  rw [h]
  have hp:0 ≤ (sourcePair w (balancedScalarSquare w)).re:=multiplier_nonnegative _ _ (fun _=>sq_nonneg _) w
  have hn:=n_pos
  have h1:0 ≤ (150*n/7)*(sourcePair w (balancedScalarSquare w)).re:=mul_nonneg (by positivity) hp
  have h2:0 ≤ (144*n/175)*‖vacuum‖^2*‖embed w‖^2:=by positivity
  nlinarith only [h1,h2]
end LowEnergy.BalancedPrimitivePayer
