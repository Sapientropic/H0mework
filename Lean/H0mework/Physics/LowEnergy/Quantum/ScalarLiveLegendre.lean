import H0mework.Physics.Coframe.ScalarMomentumCoframeReadout
import H0mework.Physics.Exterior.ScalarActionTemporalMomentumLegendreVelocity

/-! The full scalar momentum and its inverse at a live coframe. The temporal
coefficient comes from the original density and is not set to its identity-
coframe value. All scalar directions and shift terms remain present. -/
set_option autoImplicit false
namespace SourceScalarLiveLegendre
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource RawLorentzianMetricHodgeRecovery
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineScalarMomentumCoframeReadout StageNineScalarPointwiseEquation
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionSecondJetLocalActualLift
open scoped BigOperators
noncomputable section

abbrev Scalar := ScalarCoordinateCarrier
abbrev pair := scalarCoordinatePairingRe

theorem pair_symm (x y : Scalar) : pair x y = pair y x := by
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re]
  ring

theorem pair_sub_left (x y z : Scalar) : pair (x-y) z = pair x z-pair y z := by
  exact LinearMap.congr_fun (map_sub scalarCoordinatePairingReBilinear x y) z

theorem pair_sub_right (x y z : Scalar) : pair x (y-z) = pair x y-pair x z :=
  (scalarCoordinatePairingReBilinear x).map_sub y z

@[simp] theorem pair_zero_left (x : Scalar) : pair 0 x = 0 := by
  simp [pair, scalarCoordinatePairingRe]

@[simp] theorem pair_zero_right (x : Scalar) : pair x 0 = 0 := by
  simp [pair, scalarCoordinatePairingRe]

theorem pair_ext (x y : Scalar) (equal : ∀ d, pair d x = pair d y) : x = y := by
  classical
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simpa [pair, scalarCoordinatePairingRe, scalarRealBasis, PiLp.single_apply, apply_ite] using
      equal (scalarRealBasis i)
  · simpa [pair, scalarCoordinatePairingRe, scalarImaginaryBasis, PiLp.single_apply,
      Complex.mul_re, apply_ite] using equal (scalarImaginaryBasis i)

def h (e : LorentzianCoframe) : Matrix LorentzianIndex LorentzianIndex ℝ :=
  |e.det| • (lorentzianMetricOfCoframe e)⁻¹

theorem inverse_metric_symm (e : LorentzianCoframe) :
    ((lorentzianMetricOfCoframe e)⁻¹).IsSymm := by
  apply Matrix.IsSymm.inv
  simp [Matrix.IsSymm, lorentzianMetricOfCoframe, Matrix.transpose_mul,
    minkowskiInternalMetric, Matrix.mul_assoc]

def momentum (e : LorentzianCoframe) (u : LorentzianIndex → Scalar) : Scalar :=
  ∑ mu, h e 0 mu • u mu

def shiftMomentum (e : LorentzianCoframe) (w : Fin 3 → Scalar) : Scalar :=
  ∑ i, h e 0 i.succ • w i

def velocity (e : LorentzianCoframe) (pi : Scalar) (w : Fin 3 → Scalar) : Scalar :=
  (h e 0 0)⁻¹ • (pi-shiftMomentum e w)

theorem momentum_split (e : LorentzianCoframe) (u : LorentzianIndex → Scalar) :
    momentum e u = h e 0 0 • u 0 + shiftMomentum e (fun i => u i.succ) := by
  exact Fin.sum_univ_succ _

theorem reader_pairing (e : LorentzianCoframe) (u : LorentzianIndex → Scalar) (d : Scalar) :
    scalarMomentumCoframeCovariantReadout d 0 (e,u) = pair d (momentum e u) := by
  have symm := inverse_metric_symm e
  have entry (i j : LorentzianIndex) :
      (lorentzianMetricOfCoframe e)⁻¹ i j = (lorentzianMetricOfCoframe e)⁻¹ j i :=
    congrFun (congrFun symm j) i
  have summed : pair d (momentum e u) = ∑ mu, h e 0 mu * pair d (u mu) := by
    change scalarCoordinatePairingReBilinear d (∑ mu, h e 0 mu • u mu) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  rw [summed]
  change |e.det| * ((1/2:ℝ) * ∑ mu, ∑ nu,
    (lorentzianMetricOfCoframe e)⁻¹ mu nu *
      (pair (scalarVariationDifferentialDirection d 0 mu) (u nu) +
       pair (u mu) (scalarVariationDifferentialDirection d 0 nu))) = _
  have variation : scalarVariationDifferentialDirection d 0 = ![d,0,0,0] := by
    funext mu
    fin_cases mu <;> rfl
  simp only [h, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  norm_num [variation]
  rw [show (![d,0,0,0] : LorentzianIndex → Scalar) 2 = 0 by rfl,
    show (![d,0,0,0] : LorentzianIndex → Scalar) 3 = 0 by rfl]
  simp only [pair_zero_left, pair_zero_right, add_zero, zero_add, mul_zero]
  rw [pair_symm (u 0) d, pair_symm (u 1) d, pair_symm (u 2) d, pair_symm (u 3) d,
    entry 1 0, entry 2 0, entry 3 0]
  ring

theorem original_momentum (source : SmoothUnifiedSource) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (d : Scalar) :
    scalarDifferentialMomentum source C d 0 p =
      pair d (momentum (C.coframe p) (holonomicScalarCovariantDerivative C p)) := by
  rw [scalarDifferentialMomentum_eq_readout]
  exact reader_pairing _ _ _

theorem inverse_velocity (e : LorentzianCoframe) (u : LorentzianIndex → Scalar)
    (noncharacteristic : h e 0 0 ≠ 0) :
    velocity e (momentum e u) (fun i => u i.succ) = u 0 := by
  rw [velocity, momentum_split, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ noncharacteristic, one_smul]

theorem original_velocity (source : SmoothUnifiedSource) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (noncharacteristic : h (C.coframe p) 0 0 ≠ 0) :
    velocity (C.coframe p)
      (scalarActionRealDual
        (StageNineScalarActionTemporalMomentumLegendreVelocity.scalarTemporalMomentumDualAt source C p))
      (fun i => holonomicScalarCovariantDerivative C p i.succ) =
        holonomicScalarCovariantDerivative C p 0 := by
  have scalarMomentum : scalarActionRealDual
      (StageNineScalarActionTemporalMomentumLegendreVelocity.scalarTemporalMomentumDualAt source C p) =
      momentum (C.coframe p) (holonomicScalarCovariantDerivative C p) := by
    apply pair_ext
    intro d
    change scalarCoordinatePairingRe d (scalarActionRealDual _) = _
    rw [scalarCoordinatePairingRe_actionRealDual]
    exact original_momentum source C p d
  rw [scalarMomentum]
  exact inverse_velocity _ _ noncharacteristic

def localHamiltonian (a : ℝ) (b connection pi : Scalar) (spatial potential : ℝ) : ℝ :=
  (2*a)⁻¹ * pair (pi-b) (pi-b)-pair pi connection-spatial+potential

theorem Legendre_identity (a : ℝ) (noncharacteristic : a ≠ 0)
    (b connection pi : Scalar) (spatial potential : ℝ) :
    let v := a⁻¹ • (pi-b)-connection
    pair pi v - (a/2*pair (v+connection) (v+connection) +
      pair b (v+connection)+spatial-potential) =
        localHamiltonian a b connection pi spatial potential := by
  dsimp only
  simp only [sub_add_cancel, localHamiltonian, pair_sub_left, pair_sub_right,
    scalarCoordinatePairingRe_real_smul_left, scalarCoordinatePairingRe_real_smul_right]
  rw [pair_symm b pi]
  field_simp
  ring

def kinetic (e : LorentzianCoframe) (u : LorentzianIndex → Scalar) : ℝ :=
  (1/2:ℝ)*∑ mu, ∑ nu, h e mu nu*pair (u mu) (u nu)

def spatialKinetic (e : LorentzianCoframe) (w : Fin 3 → Scalar) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, h e i.succ j.succ*pair (w i) (w j)

theorem kinetic_split (e : LorentzianCoframe) (u : LorentzianIndex → Scalar) :
    kinetic e u = h e 0 0/2*pair (u 0) (u 0) +
      pair (shiftMomentum e (fun i => u i.succ)) (u 0) +
      spatialKinetic e (fun i => u i.succ) := by
  have symmetric (mu nu : LorentzianIndex) : h e mu nu = h e nu mu := by
    exact congrArg (|e.det| * ·) (congrFun (congrFun (inverse_metric_symm e) nu) mu)
  have shifted : pair (shiftMomentum e (fun i => u i.succ)) (u 0) =
      ∑ i : Fin 3, h e 0 i.succ * pair (u i.succ) (u 0) := by
    change scalarCoordinatePairingReBilinear (∑ i : Fin 3, h e 0 i.succ • u i.succ) (u 0) = _
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [shifted]
  unfold kinetic spatialKinetic
  rw [Fin.sum_univ_succ]
  have split (mu : LorentzianIndex) :
      (∑ nu, h e mu nu*pair (u mu) (u nu)) =
        h e mu 0*pair (u mu) (u 0) + ∑ j : Fin 3, h e mu j.succ*pair (u mu) (u j.succ) :=
    Fin.sum_univ_succ _
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp_rw [symmetric _ 0, pair_symm (u 0)]
  ring

theorem original_kinetic (source : SmoothUnifiedSource) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) :
    generatedVolumeDensity (toContinuumPointField C p) *
      generatedScalarKineticDensity source 0 p (toContinuumPointField C p) =
        kinetic (C.coframe p) (holonomicScalarCovariantDerivative C p) := by
  unfold generatedVolumeDensity generatedScalarKineticDensity kinetic
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    toContinuumPointField, h, Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc (|(C.coframe p).det|), ← Finset.mul_sum]
  ring

def connectionTime (C : StageNineHolonomicConfiguration) (p : BasePoint) : Scalar :=
  scalarMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed (C.gaugeConnection p 0)) (C.scalar p)

def sourceHamiltonian (source : SmoothUnifiedSource) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (pi : Scalar) : ℝ :=
  localHamiltonian (h (C.coframe p) 0 0)
    (shiftMomentum (C.coframe p) (fun i => holonomicScalarCovariantDerivative C p i.succ))
    (connectionTime C p) pi
    (spatialKinetic (C.coframe p) (fun i => holonomicScalarCovariantDerivative C p i.succ))
    (generatedVolumeDensity (toContinuumPointField C p)*generatedScalarPotential source 0 p (C.scalar p))

theorem source_Hamiltonian_is_original_Legendre
    (source : SmoothUnifiedSource) (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (noncharacteristic : h (C.coframe p) 0 0 ≠ 0) :
    sourceHamiltonian source C p (momentum (C.coframe p) (holonomicScalarCovariantDerivative C p)) =
      pair (momentum (C.coframe p) (holonomicScalarCovariantDerivative C p))
        (fieldDirectionalDerivative C.scalar p 0) -
      generatedVolumeDensity (toContinuumPointField C p) *
        (generatedScalarKineticDensity source 0 p (toContinuumPointField C p) -
         generatedScalarPotential source 0 p (C.scalar p)) := by
  let pi := momentum (C.coframe p) (holonomicScalarCovariantDerivative C p)
  have inverse := inverse_velocity (C.coframe p) (holonomicScalarCovariantDerivative C p) noncharacteristic
  have raw : (h (C.coframe p) 0 0)⁻¹ •
      (pi-shiftMomentum (C.coframe p) (fun i => holonomicScalarCovariantDerivative C p i.succ)) -
        connectionTime C p = fieldDirectionalDerivative C.scalar p 0 := by
    change velocity (C.coframe p) pi _ - connectionTime C p = _
    rw [inverse]
    exact add_sub_cancel_right _ _
  have law := Legendre_identity (h (C.coframe p) 0 0) noncharacteristic
    (shiftMomentum (C.coframe p) (fun i => holonomicScalarCovariantDerivative C p i.succ))
    (connectionTime C p) pi
    (spatialKinetic (C.coframe p) (fun i => holonomicScalarCovariantDerivative C p i.succ))
    (generatedVolumeDensity (toContinuumPointField C p)*generatedScalarPotential source 0 p (C.scalar p))
  dsimp only at law
  rw [raw] at law
  change _ = sourceHamiltonian source C p pi at law
  rw [← law, mul_sub, original_kinetic, kinetic_split]
  rfl

end
end SourceScalarLiveLegendre
