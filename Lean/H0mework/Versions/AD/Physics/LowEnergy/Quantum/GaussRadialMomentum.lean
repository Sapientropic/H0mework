import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialDomain
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceNativeRadial

/-! Original radial multiplication and all native covariant momentum domains. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussRadialMomentum
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussRadialDomain
open GaussYukawaCoefficient GaussMomentumAdjoint GaussHistoryHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff RealInnerProductSpace

def scalarCoordinate : SourceCoordinateSlice →L[ℝ] Scalar :=
  scalarSlice.subtypeL.comp ((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp
    (ContinuousLinearMap.snd ℝ SourceQuantumConfigurationHilbert.Coframe Slice))

theorem inverse_radial (z : physicalChart) (v : Ambient) :
    ⟪(z.val.2.1 : Scalar), ((inverseL z.val v).2.1 : Scalar)⟫ =
      ⟪(z.val.2.1 : Scalar), v.1⟫ := by
  have h := congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1 : Scalar)) (inverseL z.val v).1 +
    ((inverseL z.val v).2.1 : Scalar) = v.1 at h
  have hi := congrArg (fun y : Scalar => ⟪(z.val.2.1 : Scalar), y⟫) h
  rw [inner_add_right, SourceNativeHistoryRadial.radial_orbit_zero, zero_add] at hi
  exact hi

def radialDerivative (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  -⟪(z.2.1 : Scalar), v.1⟫ / (4*radius z^3)

theorem reciprocal_derivative (z : SourceCoordinateSlice) (h : SourceCoordinateSlice) :
    fderiv ℝ reciprocal z h = -⟪(z.2.1 : Scalar), (h.2.1 : Scalar)⟫ / (4*radius z^3) := by
  have hs := (((scalarCoordinate.hasFDerivAt (x := z)).norm_sq).mul_const (4⁻¹ : ℝ)).const_add 1
  simp only [← div_eq_mul_inv] at hs
  have hp : 1+‖scalarCoordinate z‖^2/4 ≠ 0 := by positivity
  have hd := (hasDerivAt_inv (radius_pos z).ne').comp_hasFDerivAt z (hs.sqrt hp)
  change fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ radius) z h = _
  rw [hd.fderiv]
  simp only [smul_apply, two_smul, smul_eq_mul]
  change (-(radius z^2)⁻¹) * ((1/(2*radius z)) * (4⁻¹ *
    (⟪(z.2.1 : Scalar), (h.2.1 : Scalar)⟫+⟪(z.2.1 : Scalar), (h.2.1 : Scalar)⟫))) = _
  field_simp
  ring

theorem direction_reciprocal (z : physicalChart) (v : Ambient) :
    fderiv ℝ reciprocal z.val (direction v z.val) = radialDerivative v z.val := by
  rw [reciprocal_derivative]
  change -⟪(z.val.2.1 : Scalar), ((inverseL z.val v).2.1 : Scalar)⟫ / _ = _
  rw [inverse_radial]
  rfl

theorem radialDerivative_smooth (v : Ambient) : ContDiff ℝ ∞ (radialDerivative v) :=
  ((scalarCoordinate.contDiff.inner ℝ contDiff_const).neg).div (contDiff_const.mul (radius_smooth.pow 3))
    (fun z => mul_ne_zero (by norm_num) (pow_ne_zero _ (radius_pos z).ne'))

theorem radialDerivative_bound (v : Ambient) (z : SourceCoordinateSlice) :
    |radialDerivative v z| ≤ ‖v.1‖/2 := by
  have hp := radius_pos z
  have h1 := one_le_radius z
  have hs := Real.sq_sqrt (show 0 ≤ 1+‖(z.2.1 : Scalar)‖^2/4 by positivity)
  change (radius z)^2 = _ at hs
  have hx : ‖(z.2.1 : Scalar)‖ ≤ 2*radius z := by nlinarith [norm_nonneg (z.2.1 : Scalar)]
  have hi := abs_real_inner_le_norm (z.2.1 : Scalar) v.1
  rw [radialDerivative, abs_div, abs_neg, abs_of_pos (show 0 < 4*radius z^3 by positivity)]
  apply (div_le_iff₀ (show 0 < 4*radius z^3 by positivity)).mpr
  have hpow : radius z ≤ radius z^3 := by nlinarith [sq_nonneg (radius z-1)]
  calc
    _ ≤ ‖(z.2.1 : Scalar)‖*‖v.1‖ := hi
    _ ≤ (2*radius z)*‖v.1‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ (‖v.1‖/2)*(4*radius z^3) := by nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg v.1)]

#print axioms inverse_radial
#print axioms direction_reciprocal
#print axioms radialDerivative_bound

theorem inverseAction_real (f : QuantumTest) :
    (inverseAction f : SourceCoordinateSlice → FockFiber) = fun z => reciprocal z • f z := by
  funext z
  apply PiLp.ext
  intro word
  change (reciprocal z : ℂ)*f z word = reciprocal z • f z word
  exact Complex.real_smul.symm

theorem directional_inverse (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (inverseAction f) z = reciprocal z • directional v f z +
      radialDerivative v z • f z := by
  rw [directional_apply, inverseAction_real,
    fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change reciprocal z • directional v f z + fderiv ℝ reciprocal z (direction v z) • f z = _
  by_cases hz : z ∈ physicalChart
  · rw [direction_reciprocal ⟨z,hz⟩]
  · have hf : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf, smul_zero, smul_zero]

def commutatorFiber (v : Ambient) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  ((-Complex.I)*(radialDerivative v z : ℂ)) • ContinuousLinearMap.id ℂ FockFiber

theorem commutator_smooth (v : Ambient) : ContDiff ℝ ∞ (commutatorFiber v) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (radialDerivative_smooth v))).smul contDiff_const

def commutatorAction (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (commutatorFiber v) (fun _ => (commutator_smooth v).contDiffAt)

theorem core_commutator (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (inverseAction f) = inverseAction (covariantMomentum v f) + commutatorAction v f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (inverseAction f) z+
    connection v z (inverseAction f z)) =
      (reciprocal z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z))) +
        ((-Complex.I)*(radialDerivative v z : ℂ)) • f z
  rw [directional_inverse]
  change (-Complex.I) • (reciprocal z • directional v f z + radialDerivative v z • f z +
    connection v z ((reciprocal z : ℂ) • f z)) = _
  rw [map_smul]
  apply PiLp.ext
  intro word
  change (-Complex.I)*((reciprocal z • directional v f z word + radialDerivative v z • f z word)+
    (reciprocal z : ℂ)*connection v z (f z) word) = _
  simp only [Complex.real_smul]
  change _ = (reciprocal z : ℂ)*((-Complex.I)*(directional v f z word+connection v z (f z) word))+
    ((-Complex.I)*(radialDerivative v z : ℂ))*f z word
  ring

theorem commutator_commutes (v : Ambient) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (commutatorFiber v z) :=
  (Commute.one_right (GaussFockWeights.weight w)).smul_right _

theorem commutator_bound (v : Ambient) (z : SourceCoordinateSlice) (f : FockFiber) :
    ‖commutatorFiber v z f‖ ≤ (‖v.1‖/2)*‖f‖ := by
  change ‖((-Complex.I)*(radialDerivative v z : ℂ)) • f‖ ≤ _
  rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (radialDerivative_bound v z) (norm_nonneg f)

def boundedCommutator (v : Ambient) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (commutatorFiber v) (fun _ => (commutator_smooth v).contDiffAt)
    (fun z => commutator_commutes v z) (‖v.1‖/2) (by positivity) (fun z => commutator_bound v z)

theorem boundedCommutator_core (v : Ambient) (f : QuantumTest) :
    boundedCommutator v (embed f) = embed (commutatorAction v f) :=
  GaussBoundedMultiplier.extension_core (commutatorFiber v) (fun _ => (commutator_smooth v).contDiffAt)
    (fun z => commutator_commutes v z) (‖v.1‖/2) (by positivity) (fun z => commutator_bound v z) f

theorem boundedCommutator_norm (v : Ambient) : ‖boundedCommutator v‖ ≤ ‖v.1‖/2 :=
  GaussBoundedMultiplier.extension_norm (commutatorFiber v) (fun _ => (commutator_smooth v).contDiffAt)
    (fun z => commutator_commutes v z) (‖v.1‖/2) (by positivity) (fun z => commutator_bound v z)

#print axioms core_commutator
#print axioms boundedCommutator_core
#print axioms boundedCommutator_norm
end LowEnergy.GaussRadialMomentum
