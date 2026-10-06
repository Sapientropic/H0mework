import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceKineticTranspose
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialHamiltonian

/-! Literal volume differentiation on the original six-coordinate coframe core. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceCoframeVolume
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussCoframeCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussLiveMomentum SourceQuantumScalarChart
open scoped ContDiff Topology InnerProductSpace

def coordinate (i : Fin 6) : SourceCoordinateSlice →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ Coframe Slice)

def volumeGradient (z : SourceCoordinateSlice) : Fin 6 → ℝ :=
  ![z.1 2*z.1 5, 0, z.1 0*z.1 5, 0, 0, z.1 0*z.1 2]

theorem volume_derivative (z h : SourceCoordinateSlice) :
    fderiv ℝ volume z h = h.1 0*z.1 2*z.1 5+z.1 0*h.1 2*z.1 5+
      z.1 0*z.1 2*h.1 5 := by
  have hd := (((coordinate 0).hasFDerivAt (x := z)).mul
    ((coordinate 2).hasFDerivAt (x := z))).mul ((coordinate 5).hasFDerivAt (x := z))
  change HasFDerivAt volume _ z at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change (z.1 0*z.1 2)*h.1 5+z.1 5*(z.1 0*h.1 2+z.1 2*h.1 0)=_
  ring

theorem volume_coordinate_derivative (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ volume z (coframeDirection i) = volumeGradient z i := by
  rw [volume_derivative]
  fin_cases i <;> simp [coframeDirection, volumeGradient]

theorem polynomial_volume (z : SourceCoordinateSlice) (i : Fin 6) :
    (∑ j : Fin 6, GaussCoframeKinetic.polynomial z.1 i j * volumeGradient z j) =
      volume z * z.1 i := by
  fin_cases i <;> simp [GaussCoframeKinetic.polynomial, volumeGradient, volume,
    Fin.sum_univ_succ] <;> ring

theorem coefficient_volume (z : physicalChart) (i : Fin 6) :
    (∑ j : Fin 6, GaussCoframeKinetic.coefficient i j z.val * volumeGradient z.val j) =
      (sourceTime 0/4)*z.val.1 i := by
  simp only [GaussCoframeKinetic.coefficient, mul_assoc, ←Finset.mul_sum]
  rw [polynomial_volume]
  field_simp [(volume_pos z).ne']

private theorem volume_gradient_smooth (i : Fin 6) :
    ContDiff ℝ ∞ (fun z => volumeGradient z i) := by
  fin_cases i <;> dsimp [volumeGradient] <;> fun_prop

def volumeAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply volume (fun _ => volume_smooth.contDiffAt)

def gradientAction (i : Fin 6) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (fun z => volumeGradient z i) (fun _ => (volume_gradient_smooth i).contDiffAt)

theorem volume_action_real (f : QuantumTest) :
    (volumeAction f : SourceCoordinateSlice → FockFiber) = fun z => volume z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

theorem derivative_volume (i : Fin 6) (f : QuantumTest) (z : SourceCoordinateSlice) :
    derivative (coframeDirection i) (volumeAction f) z =
      volume z • derivative (coframeDirection i) f z + volumeGradient z i • f z := by
  rw [derivative_apply, volume_action_real,
    fderiv_fun_smul (volume_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change volume z • fderiv ℝ f z (coframeDirection i)+
    fderiv ℝ volume z (coframeDirection i) • f z = _
  rw [volume_coordinate_derivative, derivative_apply]

theorem momentum_volume (i : Fin 6) (f : QuantumTest) :
    momentum i (volumeAction f) = volumeAction (momentum i f) +
      (-Complex.I) • gradientAction i f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • derivative (coframeDirection i) (volumeAction f) z =
    (volume z : ℂ) • ((-Complex.I) • derivative (coframeDirection i) f z) +
      (-Complex.I) • ((volumeGradient z i : ℂ) • f z)
  rw [derivative_volume]
  apply PiLp.ext
  intro word
  change (-Complex.I) * (volume z • (derivative (coframeDirection i) f z word) +
      volumeGradient z i • f z word) =
    (volume z : ℂ) * ((-Complex.I) * derivative (coframeDirection i) f z word) +
      (-Complex.I) * ((volumeGradient z i : ℂ) * f z word)
  simp only [Complex.real_smul]
  ring

theorem pair_ext (f g : QuantumTest)
    (h : ∀ a, sourcePair a f=sourcePair a g) : f=g := by
  have hz : inner ℂ (embed (f-g)) (embed (f-g))=0 := by
    change sourcePair (f-g) (f-g)=0
    unfold sourcePair
    rw [map_sub embed f g, inner_sub_right]
    exact sub_eq_zero.mpr (h (f-g))
  apply sub_eq_zero.mp
  apply embed_injective
  simpa only [map_zero] using (inner_self_eq_zero (𝕜 := ℂ)).mp hz

theorem adjoint_volume (i : Fin 6) (g : QuantumTest) :
    GaussCoframeCore.adjoint i (volumeAction g) =
      volumeAction (GaussCoframeCore.adjoint i g) + (-Complex.I) • gradientAction i g := by
  apply pair_ext
  intro f
  have hp := momentum_volume i f
  have hpoint := congrArg (fun a => sourcePair a g) hp
  change sourcePair (momentum i (volumeAction f)) g =
    sourcePair (volumeAction (momentum i f)+(-Complex.I) • gradientAction i f) g at hpoint
  change inner ℂ (embed (momentum i (volumeAction f))) (embed g) =
    inner ℂ (embed (volumeAction (momentum i f)+(-Complex.I) • gradientAction i f)) (embed g) at hpoint
  rw [map_add, map_smul, inner_add_left, inner_smul_left] at hpoint
  simp only [map_neg, Complex.conj_I, neg_neg] at hpoint
  have hU (a b : QuantumTest) : sourcePair a (volumeAction b)=sourcePair (volumeAction a) b :=
    multiply_pair _ _ a b
  have hG (a b : QuantumTest) : sourcePair a (gradientAction i b)=sourcePair (gradientAction i a) b :=
    multiply_pair _ _ a b
  change sourcePair f (GaussCoframeCore.adjoint i (volumeAction g)) =
    sourcePair f (volumeAction (GaussCoframeCore.adjoint i g)+(-Complex.I) • gradientAction i g)
  change sourcePair (momentum i (volumeAction f)) g =
    sourcePair (volumeAction (momentum i f)) g+Complex.I*sourcePair (gradientAction i f) g at hpoint
  calc
    _ = sourcePair (momentum i f) (volumeAction g) :=
      GaussCoframeKinetic.adjoint_pair i f (volumeAction g)
    _ = sourcePair (volumeAction (momentum i f)) g := hU _ _
    _ = sourcePair (momentum i (volumeAction f)) g-
        Complex.I*sourcePair (gradientAction i f) g := by linear_combination -hpoint
    _ = sourcePair (volumeAction f) (GaussCoframeCore.adjoint i g)-
        Complex.I*sourcePair f (gradientAction i g) := by
      rw [←GaussCoframeKinetic.adjoint_pair i (volumeAction f) g, ←hG f g]
    _ = sourcePair f (volumeAction (GaussCoframeCore.adjoint i g))-
        Complex.I*sourcePair f (gradientAction i g) := by rw [←hU]
    _ = _ := by
      unfold sourcePair
      rw [map_add, map_smul, inner_add_right, inner_smul_right]
      ring

def scale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice := (r • z.1,z.2)
def euler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (z.1,0)

theorem volume_scale (r : ℝ) (z : SourceCoordinateSlice) : volume (scale r z)=r^3*volume z := by
  simp only [scale, volume, PiLp.smul_apply, smul_eq_mul]
  ring

theorem density_scale (N : ℕ) (r : ℝ) (z : SourceCoordinateSlice) :
    GaussDensityCore.density N (scale r z) = r^(3*(N+2))*GaussDensityCore.density N z := by
  change jacobian (z.2.2 : Gauge) * volume (scale r z)^(N+2) =
    r^(3*(N+2))*(jacobian (z.2.2 : Gauge)*volume z^(N+2))
  rw [volume_scale, mul_pow, ←pow_mul]
  ring

private theorem scale_one (z : SourceCoordinateSlice) : scale 1 z=z := by simp [scale]

private theorem scale_derivative (z : SourceCoordinateSlice) (r : ℝ) :
    HasDerivAt (fun s => scale s z) (euler z) r := by
  have h := ((hasDerivAt_id r).smul_const z.1).prodMk (hasDerivAt_const r z.2)
  simpa only [scale, euler, id_eq, one_smul] using! h

theorem density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.density N) z.val (euler z.val) =
      (3*(N+2) : ℕ)*GaussDensityCore.density N z.val := by
  have chain := ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_derivative z.val 1) (scale_one z.val).symm
  have actual := ((hasDerivAt_id (1 : ℝ)).pow (3*(N+2))).mul_const
    (GaussDensityCore.density N z.val)
  have hactual : HasDerivAt (fun s => GaussDensityCore.density N (scale s z.val))
      ((3*(N+2) : ℕ)*GaussDensityCore.density N z.val) 1 := by
    simpa only [density_scale, Pi.pow_apply, id_eq, one_pow, mul_one] using! actual
  exact chain.unique hactual

end LowEnergy.SourceCoframeVolume
