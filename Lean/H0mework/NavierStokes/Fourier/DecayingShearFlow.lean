import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import H0mework.NavierStokes.Fourier.FilteredNavierStokesGenerator

/-!
# A nonconstant periodic decaying shear flow

For positive viscosity, this module generates the explicit lifted
three-torus trajectory

`u(t,x) = A exp(-ν (2π)² t) sin(2π x₁) e₀`.

The varying spatial coordinate and the velocity direction are transverse.
Consequently the velocity and quadratic tensor are divergence-free, while
the vector Laplacian supplies the exact exponential decay.  Zero forcing
and zero pressure therefore give an actual pointwise Navier--Stokes time
update with no PDE law supplied as a premise.

The canonical amplitude `A = 1` is proved spatially nonconstant without a
nonzero-amplitude premise.  The nonlinear divergence is nevertheless zero,
so this source is a non-silent viscous calibration, not a nonzero cascade
or turbulent-flux theorem.
-/

open scoped Laplacian

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicDecayingShearFlow

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseCorrelationResidual
open ThreeDimensionalPeriodicCoarseNonlinearDivergence
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator

noncomputable section

/-- Fundamental unit-lattice wave number. -/
noncomputable def waveNumber : ℝ :=
  2 * Real.pi

/-- Linear phase varying in physical coordinate one. -/
noncomputable def wavePhase : PhysicalSpace →L[ℝ] ℝ :=
  waveNumber • EuclideanSpace.proj (1 : Coordinate)

/-- Fundamental periodic sine mode. -/
noncomputable def waveMode (x : PhysicalSpace) : ℝ :=
  Real.sin (wavePhase x)

/-- Velocity direction, transverse to the varying coordinate. -/
noncomputable def shearDirection : PhysicalSpace :=
  EuclideanSpace.single (0 : Coordinate) 1

noncomputable def scalarSlice
    (amplitude : ℝ) : PhysicalSpace → ℝ :=
  fun x => amplitude * waveMode x

noncomputable def shearSlice
    (amplitude : ℝ) : NSVelocityField :=
  fun x => scalarSlice amplitude x • shearDirection

noncomputable def directionStress : Stress :=
  fun i j => shearDirection i * shearDirection j

noncomputable def scalarSquare
    (amplitude : ℝ) : PhysicalSpace → ℝ :=
  fun x => (scalarSlice amplitude x) ^ 2

/-- Positive viscous decay rate generated from the physical viscosity. -/
noncomputable def decayRate (ν : Viscosity) : ℝ :=
  ν.coeff * waveNumber ^ 2

noncomputable def timeAmplitude
    (ν : Viscosity) (initialAmplitude : ℝ) (t : ℝ) : ℝ :=
  initialAmplitude * Real.exp (-(decayRate ν) * t)

/-- The source-generated decaying shear trajectory. -/
noncomputable def shearVelocity
    (ν : Viscosity) (initialAmplitude : ℝ) (t : ℝ) :
    NSVelocityField :=
  shearSlice (timeAmplitude ν initialAmplitude t)

/-- The source generates no external force. -/
def shearZeroForcing : NSVelocityField :=
  0

/-- The source generates zero pressure. -/
def shearZeroPressure : NSPressureField :=
  0

/-- Point used to witness spatial nonconstancy of the canonical mode. -/
noncomputable def quarterPoint : PhysicalSpace :=
  EuclideanSpace.single (1 : Coordinate) (1 / 4 : ℝ)

theorem waveMode_latticePeriodic :
    LatticePeriodic waveMode := by
  intro z x
  unfold waveMode wavePhase waveNumber
  change Real.sin ((2 * Real.pi) *
      (x (1 : Coordinate) + (z (1 : Coordinate) : ℝ))) =
    Real.sin ((2 * Real.pi) * x (1 : Coordinate))
  rw [show (2 * Real.pi) *
      (x (1 : Coordinate) + (z (1 : Coordinate) : ℝ)) =
      (2 * Real.pi) * x (1 : Coordinate) +
        (z (1 : Coordinate) : ℝ) * (2 * Real.pi) by
    ring]
  exact Real.sin_add_int_mul_two_pi _ _

theorem shearVelocity_latticePeriodic
    (ν : Viscosity) (initialAmplitude t : ℝ) :
    LatticePeriodic
      (shearVelocity ν initialAmplitude t) := by
  intro z x
  unfold shearVelocity shearSlice scalarSlice
  rw [waveMode_latticePeriodic z x]

/-- The explicit formula supplies joint space-time `C¹` regularity. -/
theorem shearVelocity_joint_contDiff
    (ν : Viscosity) (initialAmplitude : ℝ) :
    ContDiff ℝ 1
      (fun q : ℝ × PhysicalSpace =>
        shearVelocity ν initialAmplitude q.1 q.2) := by
  unfold shearVelocity shearSlice scalarSlice timeAmplitude
    decayRate waveMode wavePhase waveNumber shearDirection
  fun_prop

/-- Every fixed time slice has the spatial `C²` regularity of the generator. -/
theorem shearVelocity_contDiff
    (ν : Viscosity) (initialAmplitude t : ℝ) :
    ContDiff ℝ 2
      (shearVelocity ν initialAmplitude t) := by
  unfold shearVelocity shearSlice scalarSlice timeAmplitude
    decayRate waveMode wavePhase waveNumber shearDirection
  fun_prop

theorem shearZeroForcing_contDiff :
    ContDiff ℝ 1 shearZeroForcing := by
  change ContDiff ℝ 1
    (fun _ : PhysicalSpace => (0 : PhysicalSpace))
  exact contDiff_const

theorem shearZeroPressure_contDiff :
    ContDiff ℝ 1 shearZeroPressure := by
  change ContDiff ℝ 1
    (fun _ : PhysicalSpace => (0 : ℝ))
  exact contDiff_const

theorem waveMode_laplacian :
    Δ waveMode =
      fun x => -(waveNumber ^ 2) * waveMode x := by
  have hphase :
      Differentiable ℝ (wavePhase : PhysicalSpace → ℝ) :=
    wavePhase.differentiable
  have hcos :
      Differentiable ℝ (fun y => Real.cos (wavePhase y)) :=
    hphase.cos
  have hfirst :
      fderiv ℝ waveMode =
        fun y => Real.cos (wavePhase y) • wavePhase := by
    funext y
    unfold waveMode
    rw [fderiv_sin (hphase y), ContinuousLinearMap.fderiv]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    waveMode (EuclideanSpace.basisFun Coordinate ℝ)]
  funext x
  simp only [iteratedFDeriv_two_apply,
    EuclideanSpace.basisFun_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hfirst]
  rw [fderiv_smul_const (hcos x) wavePhase]
  rw [fderiv_cos (hphase x)]
  simp only [ContinuousLinearMap.fderiv,
    ContinuousLinearMap.smulRight_apply,
    smul_apply]
  unfold wavePhase waveNumber waveMode
  simp only [smul_eq_mul]
  norm_num
  have hphaseValue :
      wavePhase x =
        Real.pi * x (1 : Coordinate) * 2 := by
    simp [wavePhase, waveNumber]
    ring
  rw [hphaseValue]
  ring_nf

theorem shearSlice_laplacian (amplitude : ℝ) :
    Δ (shearSlice amplitude) =
      fun x => -(waveNumber ^ 2) • shearSlice amplitude x := by
  have hmode : ContDiff ℝ 2 waveMode := by
    unfold waveMode
    exact Real.contDiff_sin.comp wavePhase.contDiff
  have hscalar : ContDiff ℝ 2 (scalarSlice amplitude) := by
    unfold scalarSlice
    fun_prop
  have hscalarLaplacian :
      Δ (scalarSlice amplitude) =
        fun x => -(waveNumber ^ 2) * scalarSlice amplitude x := by
    funext x
    change Δ (amplitude • waveMode) x = _
    rw [InnerProductSpace.laplacian_smul
      amplitude hmode.contDiffAt, waveMode_laplacian]
    simp only [smul_eq_mul, scalarSlice]
    ring
  funext x
  change Δ
    ((ContinuousLinearMap.toSpanSingleton ℝ shearDirection) ∘
      scalarSlice amplitude) x = _
  rw [hscalar.contDiffAt.laplacian_CLM_comp_left]
  rw [hscalarLaplacian]
  simp [shearSlice,
    ContinuousLinearMap.toSpanSingleton_apply, smul_smul]

theorem shearSlice_velocityDivergence
    (amplitude : ℝ) :
    velocityDivergence (shearSlice amplitude) = 0 := by
  have hphase :
      Differentiable ℝ (wavePhase : PhysicalSpace → ℝ) :=
    wavePhase.differentiable
  have hmode : Differentiable ℝ waveMode := by
    unfold waveMode
    exact hphase.sin
  have hscalar :
      Differentiable ℝ (scalarSlice amplitude) := by
    unfold scalarSlice
    fun_prop
  have hmodeDerivative :
      fderiv ℝ waveMode =
        fun x => Real.cos (wavePhase x) • wavePhase := by
    funext x
    unfold waveMode
    rw [fderiv_sin (hphase x), ContinuousLinearMap.fderiv]
  have hscalarDerivative :
      fderiv ℝ (scalarSlice amplitude) =
        fun x => amplitude • fderiv ℝ waveMode x := by
    funext x
    change fderiv ℝ (amplitude • waveMode) x = _
    rw [fderiv_const_smul (hmode x)]
  have hshearDerivative :
      fderiv ℝ (shearSlice amplitude) =
        fun x =>
          (fderiv ℝ (scalarSlice amplitude) x).smulRight
            shearDirection := by
    funext x
    unfold shearSlice
    rw [fderiv_smul_const (hscalar x) shearDirection]
  unfold velocityDivergence
  funext x
  rw [hshearDerivative, hscalarDerivative, hmodeDerivative]
  unfold velocityDivergenceReadout
    velocityDivergenceReadoutLinear
  unfold wavePhase shearDirection
  simp [Fin.sum_univ_succ]

theorem shearSlice_tensorDivergence
    (amplitude : ℝ) :
    tensorDivergence (velocityTensor (shearSlice amplitude)) = 0 := by
  have hphase :
      Differentiable ℝ (wavePhase : PhysicalSpace → ℝ) :=
    wavePhase.differentiable
  have hmode : Differentiable ℝ waveMode := by
    unfold waveMode
    exact hphase.sin
  have hscalar :
      Differentiable ℝ (scalarSlice amplitude) := by
    unfold scalarSlice
    fun_prop
  have hsquare :
      Differentiable ℝ (scalarSquare amplitude) := by
    unfold scalarSquare
    fun_prop
  have hmodeDerivative :
      fderiv ℝ waveMode =
        fun x => Real.cos (wavePhase x) • wavePhase := by
    funext x
    unfold waveMode
    rw [fderiv_sin (hphase x), ContinuousLinearMap.fderiv]
  have hscalarDerivative :
      fderiv ℝ (scalarSlice amplitude) =
        fun x => amplitude • fderiv ℝ waveMode x := by
    funext x
    change fderiv ℝ (amplitude • waveMode) x = _
    rw [fderiv_const_smul (hmode x)]
  have hsquareDerivative :
      fderiv ℝ (scalarSquare amplitude) =
        fun x => (2 * scalarSlice amplitude x) •
          fderiv ℝ (scalarSlice amplitude) x := by
    funext x
    unfold scalarSquare
    rw [show (fun y => scalarSlice amplitude y ^ 2) =
      (scalarSlice amplitude) ^ 2 by
      rfl]
    rw [fderiv_pow 2 (hscalar x)]
    norm_num
  have htensor :
      velocityTensor (shearSlice amplitude) =
        fun x => scalarSquare amplitude x • directionStress := by
    funext x i j
    unfold velocityTensor shearSlice scalarSquare directionStress
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have htensorDerivative :
      fderiv ℝ (velocityTensor (shearSlice amplitude)) =
        fun x =>
          (fderiv ℝ (scalarSquare amplitude) x).smulRight
            directionStress := by
    rw [htensor]
    funext x
    rw [fderiv_smul_const (hsquare x) directionStress]
  unfold tensorDivergence
  funext x
  ext i
  rw [htensorDerivative, hsquareDerivative,
    hscalarDerivative, hmodeDerivative]
  unfold wavePhase directionStress shearDirection
  simp

theorem shearZeroPressure_scalarGradient :
    scalarGradient shearZeroPressure = 0 := by
  change scalarGradient
    (fun _ : PhysicalSpace => (0 : ℝ)) = 0
  funext x
  ext i
  simp [scalarGradient,
    scalarGradientReadout, scalarGradientReadoutLinear]

theorem timeAmplitude_hasDerivAt
    (ν : Viscosity) (initialAmplitude t : ℝ) :
    HasDerivAt (timeAmplitude ν initialAmplitude)
      (-(decayRate ν) *
        timeAmplitude ν initialAmplitude t) t := by
  have h :=
    (((hasDerivAt_id t).const_mul
      (-(decayRate ν))).exp).const_mul initialAmplitude
  convert h using 1
  · rfl
  · rfl
  · funext y
    rfl
  · dsimp [timeAmplitude]
    ring

theorem shearVelocity_hasDerivAt
    (ν : Viscosity) (initialAmplitude t : ℝ)
    (x : PhysicalSpace) :
    HasDerivAt
      (fun r => shearVelocity ν initialAmplitude r x)
      ((-(decayRate ν) *
        timeAmplitude ν initialAmplitude t) •
        (waveMode x • shearDirection)) t := by
  have h :=
    (timeAmplitude_hasDerivAt ν initialAmplitude t).smul_const
      (waveMode x • shearDirection)
  simpa only [shearVelocity, shearSlice, scalarSlice,
    smul_smul, smul_eq_mul] using h

theorem shearVelocity_generator
    (ν : Viscosity) (initialAmplitude t : ℝ) :
    navierStokesSpatialGenerator ν shearZeroForcing
        shearZeroPressure
        (shearVelocity ν initialAmplitude t) =
      fun x =>
        (-(decayRate ν) *
          timeAmplitude ν initialAmplitude t) •
          (waveMode x • shearDirection) := by
  rw [navierStokesSpatialGenerator]
  change ν.coeff •
        Δ (shearSlice (timeAmplitude ν initialAmplitude t)) +
      shearZeroForcing -
      tensorDivergence
        (velocityTensor
          (shearSlice (timeAmplitude ν initialAmplitude t))) -
      scalarGradient shearZeroPressure = _
  rw [shearSlice_laplacian, shearSlice_tensorDivergence,
    shearZeroPressure_scalarGradient]
  funext x
  simp only [shearZeroForcing, Pi.zero_apply, add_zero,
    Pi.smul_apply, Pi.sub_apply, sub_zero,
    shearSlice, scalarSlice]
  unfold decayRate
  simp only [smul_smul]
  ring_nf

/--
Actual pointwise Navier--Stokes update of the nonconstant periodic shear.
-/
theorem shearVelocity_actual_update
    (ν : Viscosity) (initialAmplitude t : ℝ)
    (x : PhysicalSpace) :
    HasDerivAt
      (fun r => shearVelocity ν initialAmplitude r x)
      (navierStokesSpatialGenerator ν shearZeroForcing
        shearZeroPressure
        (shearVelocity ν initialAmplitude t) x) t := by
  rw [shearVelocity_generator ν initialAmplitude t]
  exact
    shearVelocity_hasDerivAt
      ν initialAmplitude t x

/--
The fixed unit-amplitude source is spatially nonconstant at every time.
Nontriviality is generated from the exponential and sine formulas.
-/
theorem canonical_shearVelocity_not_spatially_constant
    (ν : Viscosity) (t : ℝ) :
    shearVelocity ν 1 t quarterPoint ≠
      shearVelocity ν 1 t 0 := by
  intro h
  have hzero :=
    congrArg
      (fun v : PhysicalSpace => v (0 : Coordinate)) h
  simp [shearVelocity, shearSlice, scalarSlice, waveMode,
    wavePhase, waveNumber, quarterPoint, shearDirection] at hzero
  rcases hzero with hamplitude | hsine
  · have hexponential :
        Real.exp (-(decayRate ν) * t) = 0 := by
      simpa only [timeAmplitude, one_mul] using hamplitude
    exact Real.exp_ne_zero _ hexponential
  · have hangle :
        2 * Real.pi * (4 : ℝ)⁻¹ = Real.pi / 2 := by
      ring
    rw [hangle, Real.sin_pi_div_two] at hsine
    norm_num at hsine

end

end ThreeDimensionalPeriodicDecayingShearFlow
end NavierStokes
end SaturationMonoid
