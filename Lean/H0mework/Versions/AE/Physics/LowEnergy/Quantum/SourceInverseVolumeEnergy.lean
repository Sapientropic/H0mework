import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeBulk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseNativeEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient
open GaussNativePotential GaussLiveMomentum SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceHamiltonianVolume SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceScalarNativeComparison
open SourceMixedNativeReturn SourceGammaNativeBudget SourceClosedCostNativeProbe
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarInverseBulk
open GaussUnitaryHistory FullYSourceResolventGraphSplice SourceScalarRetardedGram
open scoped ContDiff InnerProductSpace BigOperators
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := SourceScalarGaugeScale.End

private theorem inverse_volume (f : QuantumTest) : inverseVolumeAction (volumeAction f)=f := by
  have hc : Commute inverseVolumeAction volumeAction := real_volume _ _
  exact (LinearMap.congr_fun hc.eq f).trans (volume_inverse f)

private theorem inverse_commute (A : End) (h : Commute A volumeAction) :
    Commute A inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,inverse_volume] using! he.symm

theorem original_native_inverse_commute (v : Ambient) :
    Commute (covariantMomentum v) inverseVolumeAction :=
  inverse_commute _ (native_momentum_volume v)

private theorem bulk_volume : Commute positiveBulk volumeAction := by
  rw [original_positive_bulk]
  exact ((scalar_kinetic_volume.smul_left (-8 : ℂ)).add_left
    (gauge_kinetic_volume.smul_left (36 : ℂ))).add_left
      ((real_volume _ _).smul_left (8 : ℂ))

def inverseForm (f : QuantumTest) : ℝ :=
  (sourcePair f (inverseWeightedBulkJet inverseSymmetricScale f)).re

/-- The actual inverse-volume Ward form consumes the original positive form at V f. -/
theorem original_inverse_form_weighted (f : QuantumTest) :
    inverseForm f=weightedBulkForm (inverseVolumeAction f) := by
  unfold inverseForm weightedBulkForm
  rw [original_inverse_bulk_symmetric_jet,original_positive_bulk_symmetric_jet]
  change (sourcePair f (inverseVolumeAction (positiveBulk f))).re=
    (sourcePair (inverseVolumeAction f) (volumeAction (positiveBulk (inverseVolumeAction f)))).re
  have hc := LinearMap.congr_fun (inverse_commute positiveBulk bulk_volume).eq f
  simp only [Module.End.mul_apply] at hc
  rw [hc,volume_inverse]
  exact congrArg Complex.re (multiply_pair _ _ _ _)

def inverseNativeEnergy (f : QuantumTest) : ℝ :=
  ∑ a : ScalarIndex,‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖^2

theorem original_inverse_native_return (f : QuantumTest) :
    nativeScalarEnergy (inverseVolumeAction f)=inverseNativeEnergy f := by
  unfold nativeScalarEnergy inverseNativeEnergy
  apply Finset.sum_congr rfl
  intro a _
  have hc : covariantMomentum (scalarDirection a) (inverseVolumeAction f)=
      inverseVolumeAction (covariantMomentum (scalarDirection a) f) :=
    LinearMap.congr_fun (original_native_inverse_commute (scalarDirection a)).eq f
  rw [hc]

/-- No additional volume weight remains on the seventy native momentum rows. -/
theorem original_inverse_native_bound (f : QuantumTest) :
    4*sourceTime 0*inverseNativeEnergy f ≤ inverseForm f := by
  rw [original_inverse_form_weighted,←original_inverse_native_return]
  exact original_native_bulk_bound _

theorem original_inverse_nonnegative (f : QuantumTest) : 0 ≤ inverseForm f := by
  rw [original_inverse_form_weighted]
  exact original_weighted_bulk_nonnegative _

def shiftedCoordinate (a : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarField z-(1/2 : ℝ) • vacuum) (scalarBasis a)

private theorem shifted_coordinate_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (shiftedCoordinate a) :=
  (scalarField_smooth.sub contDiff_const).inner ℝ contDiff_const

def shiftedColumn (a : ScalarIndex) : End :=
  multiply (shiftedCoordinate a) (fun _ => (shifted_coordinate_smooth a).contDiffAt)

def shiftedMoment (f : QuantumTest) : ℝ := ∑ a : ScalarIndex,‖embed (shiftedColumn a f)‖^2

private theorem shifted_square (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,(shiftedCoordinate a z)^2)=‖scalarField z-(1/2 : ℝ) • vacuum‖^2 :=
  scalarBasis.sum_sq_inner_left _

private theorem shifted_column_square (f : QuantumTest) (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,shiftedColumn a (shiftedColumn a f)) z=
      ((‖scalarField z-(1/2 : ℝ) • vacuum‖^2 : ℝ) : ℂ) • f z := by
  simp only [sum_apply]
  change (∑ a : ScalarIndex,(shiftedCoordinate a z : ℂ) • ((shiftedCoordinate a z : ℂ) • f z))=_
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [shifted_square]

theorem original_inverse_shifted_square (f : QuantumTest) :
    inverseVolumeAction (shiftedAction f)=(sourceTime 0 : ℂ) •
      ∑ a : ScalarIndex,shiftedColumn a (shiftedColumn a f) := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z : ℂ) • ((shiftedPotential z : ℂ) • f z)=
    (sourceTime 0 : ℂ) • (∑ a : ScalarIndex,shiftedColumn a (shiftedColumn a f)) z
  rw [shifted_column_square,smul_smul,smul_smul,←Complex.ofReal_mul,←Complex.ofReal_mul]
  by_cases hz : z ∈ physicalChart
  · apply congrArg (fun c : ℝ => (c : ℂ) • f z)
    unfold reciprocalVolume shiftedPotential
    field_simp [(volume_pos ⟨z,hz⟩).ne']
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)),smul_zero,smul_zero]

theorem original_inverse_shifted_form (f : QuantumTest) :
    (sourcePair (inverseRootAction f) (shiftedAction (inverseRootAction f))).re=
      sourceTime 0*shiftedMoment f := by
  have hcomm : Commute inverseRootAction shiftedAction := inverse_root_real _ _
  have hc := LinearMap.congr_fun hcomm.eq (inverseRootAction f)
  change inverseRootAction (shiftedAction (inverseRootAction f))=
    shiftedAction (inverseRootAction (inverseRootAction f)) at hc
  have hp := (multiply_pair inverseRootVolume inverse_root_volume_smooth f
    (shiftedAction (inverseRootAction f))).symm
  change sourcePair (inverseRootAction f) (shiftedAction (inverseRootAction f))=
    sourcePair f (inverseRootAction (shiftedAction (inverseRootAction f))) at hp
  have hi : Commute inverseVolumeAction shiftedAction := by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z : ℂ) (shiftedPotential z : ℂ) (q z)
  have hif := LinearMap.congr_fun hi.eq f
  simp only [Module.End.mul_apply] at hif
  rw [hc,inverse_root_square,←hif,original_inverse_shifted_square] at hp
  have hs (a : ScalarIndex) : sourcePair f (shiftedColumn a (shiftedColumn a f))=
      sourcePair (shiftedColumn a f) (shiftedColumn a f) := multiply_pair _ _ _ _
  have hr := congrArg Complex.re hp
  simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum] at hr
  change _=((sourceTime 0 : ℂ)*∑ a : ScalarIndex,sourcePair f (shiftedColumn a (shiftedColumn a f))).re at hr
  simp_rw [hs] at hr
  have hsreal (q : QuantumTest) : (sourcePair q q).re=‖embed q‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (embed q)
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.re_sum,hsreal,shiftedMoment] using! hr

/-- Exact source cost: V P_i, the original electric form, and the unweighted shifted scalar field. -/
theorem original_inverse_energy (f : QuantumTest) :
    inverseForm f=4*sourceTime 0*inverseNativeEnergy f+
      36*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
      8*sourceTime 0*shiftedMoment f := by
  rw [original_inverse_form_weighted,original_weighted_bulk_form,volume_inverse,
    original_inverse_native_return,original_inverse_shifted_form]
  ring

theorem original_inverse_shifted_bound (f : QuantumTest) :
    8*sourceTime 0*shiftedMoment f ≤ inverseForm f := by
  rw [original_inverse_energy]
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have he := original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hm : 0 ≤ inverseNativeEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

private theorem scalar_column_split (a : ScalarIndex) (f : QuantumTest) :
    scalarColumn a f=shiftedColumn a f-
      ((inner ℝ vacuum (scalarBasis a)/2 : ℝ) : ℂ) • f := by
  apply DFunLike.ext
  intro z
  change (inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z=
    (shiftedCoordinate a z : ℂ) • f z-((inner ℝ vacuum (scalarBasis a)/2 : ℝ) : ℂ) • f z
  rw [←sub_smul,←Complex.ofReal_sub]
  apply congrArg (fun c : ℝ => (c : ℂ) • f z)
  unfold shiftedCoordinate scalarField
  rw [inner_sub_left,inner_add_left,real_inner_smul_left]
  ring

private theorem norm_sub_square {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x-y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem original_scalar_moment_bound (f : QuantumTest) :
    scalarMoment f ≤ 2*shiftedMoment f+(‖vacuum‖^2/2)*‖embed f‖^2 := by
  have h (a : ScalarIndex) : ‖embed (scalarColumn a f)‖^2 ≤
      2*(‖embed (shiftedColumn a f)‖^2+
        (inner ℝ vacuum (scalarBasis a)/2)^2*‖embed f‖^2) := by
    rw [scalar_column_split,map_sub,map_smul]
    simpa only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      norm_sub_square (embed (shiftedColumn a f))
        (((inner ℝ vacuum (scalarBasis a)/2 : ℝ) : ℂ) • embed f)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ScalarIndex)) (fun a _ => h a)
  have hc : (∑ a : ScalarIndex,(inner ℝ vacuum (scalarBasis a)/2)^2)=‖vacuum‖^2/4 := by
    simp_rw [div_pow]
    rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left vacuum]
    norm_num
  change scalarMoment f ≤ _ at hs
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul,hc] at hs
  exact hs.trans_eq (by change 2*(shiftedMoment f+_) = _; ring)

def coefficientCost (sharp : Bool) : ℝ :=
  ∑ a : ScalarIndex,‖constantBounded sharp (scalarBasis a)‖^2

private theorem coefficient_nonnegative (sharp : Bool) : 0 ≤ coefficientCost sharp :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem finite_column_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (a : ι → E →L[ℂ] E) (x : ι → E) :
    ‖∑ i,a i (x i)‖^2 ≤ (∑ i,‖a i‖^2)*(∑ i,‖x i‖^2) := by
  have h := (norm_sum_le Finset.univ (fun i : ι => a i (x i))).trans
    (Finset.sum_le_sum (fun i _ => (a i).le_opNorm (x i)))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖x i‖))

theorem original_weighted_momentum (v : Ambient) :
    weightedMomentum v=(sourceTime 0 : ℂ) • (inverseVolumeAction*covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.inverseVolume z : ℂ) • covariantMomentum v f z=
    (sourceTime 0 : ℂ) • ((reciprocalVolume z : ℂ) • covariantMomentum v f z)
  rw [smul_smul,←Complex.ofReal_mul]
  simp only [GaussCoframeForm.inverseVolume,reciprocalVolume,div_eq_mul_inv]

private theorem primitive_columns (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    embed (primitive sharp m ell f)=(sourceTime 0 : ℂ) •
      ∑ a : ScalarIndex,constantBounded sharp (scalarBasis a)
        (embed (inverseVolumeAction (covariantMomentum (scalarDirection a) (thetaAction m ell f)))) := by
  simp only [primitive,LinearMap.sum_apply,map_sum,Module.End.mul_apply,original_weighted_momentum,
    LinearMap.smul_apply,map_smul,←Finset.smul_sum]
  apply congrArg (fun x : H => (sourceTime 0 : ℂ) • x)
  exact Finset.sum_congr rfl (fun a _ => (constant_bounded_core sharp (scalarBasis a) _).symm)

/-- The original Gamma primitive carries n/U; its source factor n is retained. -/
theorem original_primitive_native_bound (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    ‖embed (primitive sharp m ell f)‖^2 ≤
      (sourceTime 0)^2*coefficientCost sharp*inverseNativeEnergy (thetaAction m ell f) := by
  rw [primitive_columns,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left
    (finite_column_estimate (fun a : ScalarIndex => constantBounded sharp (scalarBasis a))
      (fun a => embed (inverseVolumeAction (covariantMomentum (scalarDirection a) (thetaAction m ell f)))))
    (sq_nonneg (sourceTime 0))).trans_eq (by unfold coefficientCost inverseNativeEnergy; ring)

/-- Direct consumer of the source Ward form for the actual cutoff primitive. -/
theorem original_primitive_inverse_bound (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    4*sourceTime 0*‖embed (primitive sharp m ell f)‖^2 ≤
      (sourceTime 0)^2*coefficientCost sharp*inverseForm (thetaAction m ell f) := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h := mul_le_mul_of_nonneg_left (original_primitive_native_bound sharp m ell f)
    (show 0 ≤ 4*sourceTime 0 by positivity)
  have hb := mul_le_mul_of_nonneg_left (original_inverse_native_bound (thetaAction m ell f))
    (mul_nonneg (sq_nonneg (sourceTime 0)) (coefficient_nonnegative sharp))
  nlinarith only [h,hb]

theorem original_scalar_inverse_bound (sharp : Bool) (f : QuantumTest) :
    4*sourceTime 0*‖embed (scalarAction sharp f)‖^2 ≤
      coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*‖embed f‖^2) := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h0 := scalar_insertion_estimate sharp f
  change ‖embed (scalarAction sharp f)‖^2 ≤ coefficientCost sharp*scalarMoment f at h0
  have h1 := mul_le_mul_of_nonneg_left (original_scalar_moment_bound f) (coefficient_nonnegative sharp)
  have h2 := mul_le_mul_of_nonneg_left (original_inverse_shifted_bound f) (coefficient_nonnegative sharp)
  have h3 := mul_le_mul_of_nonneg_left (h0.trans h1) (show 0 ≤ 4*sourceTime 0 by positivity)
  nlinarith only [h2,h3]

/-- Both actual source mouths consume one inverse Ward form of the same cutoff vector. -/
theorem original_coupled_inverse_bound (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    4*sourceTime 0*(‖embed (primitive sharp m ell f)‖^2+
      (sourceTime 0)^2*‖embed (scalarAction sharp (thetaAction m ell f))‖^2) ≤
      2*(sourceTime 0)^2*coefficientCost sharp*(inverseForm (thetaAction m ell f)+
        sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell f)‖^2) := by
  have hp := original_primitive_inverse_bound sharp m ell f
  have hs := mul_le_mul_of_nonneg_left
    (original_scalar_inverse_bound sharp (thetaAction m ell f)) (sq_nonneg (sourceTime 0))
  nlinarith only [hp,hs]

private theorem pair_square (f g : QuantumTest) :
    ‖sourcePair f g‖^2 ≤ ‖embed f‖^2*‖embed g‖^2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (embed f) (embed g)) 2).trans_eq
    (mul_pow _ _ _)

/-- The complete two-sided primitive current is bounded by the same source forms of both cutoff legs. -/
theorem original_paired_primitive_inverse_bound (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    4*sourceTime 0*‖sourcePair p (primitive sharp m ell q)-
      sourcePair (primitive (!sharp) m ell p) q‖^2 ≤
      2*(sourceTime 0)^2*(coefficientCost sharp*‖embed p‖^2*inverseForm (thetaAction m ell q)+
        coefficientCost (!sharp)*‖embed q‖^2*inverseForm (thetaAction m ell p)) := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp := mul_le_mul_of_nonneg_left (original_primitive_inverse_bound sharp m ell q)
    (sq_nonneg ‖embed p‖)
  have hq := mul_le_mul_of_nonneg_left (original_primitive_inverse_bound (!sharp) m ell p)
    (sq_nonneg ‖embed q‖)
  have hleft := mul_le_mul_of_nonneg_left (pair_square p (primitive sharp m ell q))
    (show 0 ≤ 4*sourceTime 0 by positivity)
  have hright := mul_le_mul_of_nonneg_left (pair_square (primitive (!sharp) m ell p) q)
    (show 0 ≤ 4*sourceTime 0 by positivity)
  have hsub := mul_le_mul_of_nonneg_left
    (norm_sub_square (sourcePair p (primitive sharp m ell q))
      (sourcePair (primitive (!sharp) m ell p) q)) (show 0 ≤ 4*sourceTime 0 by positivity)
  nlinarith only [hp,hq,hleft,hright,hsub]

theorem original_paired_scalar_inverse_bound (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    4*sourceTime 0*‖sourcePair p (scalarAction sharp (thetaAction m ell q))‖^2 ≤
      coefficientCost sharp*‖embed p‖^2*(inverseForm (thetaAction m ell q)+
        2*sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell q)‖^2) := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp := mul_le_mul_of_nonneg_left (original_scalar_inverse_bound sharp (thetaAction m ell q))
    (sq_nonneg ‖embed p‖)
  have hs := mul_le_mul_of_nonneg_left (pair_square p (scalarAction sharp (thetaAction m ell q)))
    (show 0 ≤ 4*sourceTime 0 by positivity)
  nlinarith only [hp,hs]

/-- The original conjugate/nonconjugate resolvent pair directly consumes the source scalar bound. -/
theorem actual_paired_scalar_inverse_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let p := leftState F z hz k
    let q := rightState F z hz g
    4*sourceTime 0*‖sourcePair p (scalarAction sharp (thetaAction m ell q))‖^2 ≤
      coefficientCost sharp*‖embed p‖^2*(inverseForm (thetaAction m ell q)+
        2*sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell q)‖^2) :=
  original_paired_scalar_inverse_bound sharp m ell (leftState F z hz k) (rightState F z hz g)

end LowEnergy.SourceScalarInverseNativeEnergy
