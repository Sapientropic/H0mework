import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.KernelRecovery
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace Filter
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.Elementwise

private theorem matrix_mul_hasDerivAt {n m p : Type*}
    [Fintype n] [Fintype m] [Fintype p]
    (left : ℝ → Matrix n m ℂ) (right : ℝ → Matrix m p ℂ)
    (leftRate : Matrix n m ℂ) (rightRate : Matrix m p ℂ) (point : ℝ)
    (leftDerivative : HasDerivAt left leftRate point)
    (rightDerivative : HasDerivAt right rightRate point) :
    HasDerivAt (fun time => left time * right time)
      (leftRate * right point + left point * rightRate) point := by
  apply hasDerivAt_pi.mpr
  intro first
  apply hasDerivAt_pi.mpr
  intro last
  have generated := HasDerivAt.fun_sum (u := Finset.univ) (fun middle _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp leftDerivative first)) middle).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp rightDerivative middle)) last))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using! generated

private theorem matrix_conjTranspose_hasDerivAt {n m : Type*} [Fintype n] [Fintype m]
    (value : ℝ → Matrix n m ℂ) (rate : Matrix n m ℂ) (point : ℝ)
    (derivative : HasDerivAt value rate point) :
    HasDerivAt (fun time => (value time).conjTranspose) rate.conjTranspose point := by
  apply hasDerivAt_pi.mpr
  intro first
  apply hasDerivAt_pi.mpr
  intro second
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp derivative second)) first).star

/-- The actual Cayley equation supplies its difference quotient on the full source span. -/
theorem response_difference (state : Snapshot) (time : ℝ) :
    responseCoordinates state time - coordinates state =
      time • ((-Complex.I / 2 : ℂ) •
        (fullFock state * (responseCoordinates state time + coordinates state))) := by
  have equation : responseCoordinates state time + (Complex.I * ((time / 2 : ℝ) : ℂ)) •
      (fullFock state * responseCoordinates state time) =
      coordinates state - (Complex.I * ((time / 2 : ℝ) : ℂ)) •
        (fullFock state * coordinates state) := by
    simpa only [CPS1ElectronicEvolution.denominator, CPS1ElectronicEvolution.generator,
      Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] using response_equation state time
  rw [Matrix.mul_add]
  ext first slot
  have entry := congrFun (congrFun equation first) slot
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    RCLike.real_smul_eq_coe_mul, Complex.ofReal_div, Complex.ofReal_ofNat] at entry ⊢
  linear_combination entry

theorem response_coordinates_hasDerivAt (state : Snapshot) :
    HasDerivAt (responseCoordinates state)
      (-Complex.I • (fullFock state * coordinates state)) 0 := by
  have productContinuous : ContinuousAt
      (fun time : ℝ => fullFock state * (responseCoordinates state time + coordinates state)) 0 :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 continuousAt_const
      ((response_coordinates_continuous state 0).add continuousAt_const)
  have quotientContinuous : ContinuousAt (fun time : ℝ =>
      (-Complex.I / 2 : ℂ) •
        (fullFock state * (responseCoordinates state time + coordinates state))) 0 :=
    by simpa only [Pi.smul_apply] using!
      (continuousAt_const (y := (-Complex.I / 2 : ℂ))).smul productContinuous
  have atZero : (-Complex.I / 2 : ℂ) •
      (fullFock state * (responseCoordinates state 0 + coordinates state)) =
      -Complex.I • (fullFock state * coordinates state) := by
    rw [response_coordinates_zero, Matrix.mul_add, smul_add, ← add_smul]
    congr 1
    ring
  have slopeLimit : Tendsto (fun time : ℝ =>
      time⁻¹ • (responseCoordinates state (0 + time) - responseCoordinates state 0))
      (𝓝[≠] 0) (𝓝 (-Complex.I • (fullFock state * coordinates state))) := by
    have limit := quotientContinuous.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    rw [atZero] at limit
    apply limit.congr'
    filter_upwards [self_mem_nhdsWithin] with time nonzero
    have ne : time ≠ 0 := nonzero
    simp only [zero_add, response_coordinates_zero, response_difference]
    exact (inv_smul_smul₀ ne _).symm
  simpa only using! (hasDerivAt_iff_tendsto_slope_zero.mpr slopeLimit)

theorem response_density_hasDerivAt (state : Snapshot) :
    HasDerivAt (responseDensity state)
      (-Complex.I • (fullFock state * sourceDensity state - sourceDensity state * fullFock state)) 0 := by
  have generated := matrix_mul_hasDerivAt (responseCoordinates state)
    (fun time => (responseCoordinates state time).conjTranspose)
    (-Complex.I • (fullFock state * coordinates state))
    (-Complex.I • (fullFock state * coordinates state)).conjTranspose 0
    (response_coordinates_hasDerivAt state)
    (matrix_conjTranspose_hasDerivAt _ _ _ (response_coordinates_hasDerivAt state))
  have rate : (-Complex.I • (fullFock state * coordinates state)) *
        (coordinates state).conjTranspose + coordinates state *
        (-Complex.I • (fullFock state * coordinates state)).conjTranspose =
      -Complex.I • (fullFock state * sourceDensity state - sourceDensity state * fullFock state) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, (full_fock_hermitian state).eq]
    simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    simp only [sourceDensity, Matrix.mul_assoc, smul_sub, neg_smul, sub_neg_eq_add]
  simpa only [responseDensity, response_coordinates_zero, rate] using! generated

theorem response_occupation_hasDerivAt (state : Snapshot) :
    HasDerivAt (fun time : ℝ => increment state (responseCoordinates state time))
      (-Complex.I • (sourceCoefficient state * (fullFock state * coordinates state))) 0 := by
  have difference := (response_coordinates_hasDerivAt state).sub_const (coordinates state)
  have generated := matrix_mul_hasDerivAt (fun _ : ℝ => sourceCoefficient state)
    (fun time => responseCoordinates state time - coordinates state) 0
    (-Complex.I • (fullFock state * coordinates state)) 0 (hasDerivAt_const 0 _) difference
  have incrementDerivative := (hasDerivAt_const (0 : ℝ) state.occupied).add generated
  simpa only [increment, Matrix.zero_mul, zero_add, Matrix.mul_smul] using! incrementDerivative

/-- The nonlinear stored energy is stationary to first order along its own full Fock response. -/
theorem actual_response_energy_hasDerivAt (state : Snapshot) :
    HasDerivAt (fun time : ℝ => (response state time).energy) 0 0 := by
  let direction : Matrix state.PrimitiveIndex state.ElectronIndex ℂ :=
    -Complex.I • (sourceCoefficient state * (fullFock state * coordinates state))
  have energyAtCurve : HasFDerivAt
      (fun next : Matrix state.PrimitiveIndex state.ElectronIndex ℂ => (withOccupation state next).energy)
      (Polynomial.occupiedDifferential (rawCore state) (rawTensor state) state.occupied)
      (increment state (responseCoordinates state 0)) := by
    simpa only [response_coordinates_zero, increment_current] using actual_energy_hasFDerivAt state state.occupied
  have actual := energyAtCurve.comp_hasDerivAt (0 : ℝ) (response_occupation_hasDerivAt state)
  have evaluation : Polynomial.occupiedDifferential (rawCore state) (rawTensor state) state.occupied direction =
      2 * (Matrix.trace (state.occupied.conjTranspose * rawFock state * direction)).re := by
    rw [Polynomial.occupied_differential_apply,
      CPS1Deformation.FiniteVariation.density_energy_rate_fock _ _ (tensor_swap state)]
    exact CPS1Deformation.FiniteVariation.density_rate_trace _ _ _ (raw_fock_hermitian state)
  have recovered := congrArg Matrix.conjTranspose (KernelRecovery.raw_fock_current_coordinates state)
  simp only [Matrix.conjTranspose_mul, (raw_fock_hermitian state).eq, Matrix.mul_assoc] at recovered
  have frame : state.occupied.conjTranspose * rawFock state * sourceCoefficient state =
      (coordinates state).conjTranspose * fullFock state := by
    rw [recovered]
    simp only [fullFock, Matrix.mul_assoc]
  let square : ℂ := Matrix.trace
    ((fullFock state * coordinates state).conjTranspose * (fullFock state * coordinates state))
  have squareStar : star square = square := by
    change star (Matrix.trace _) = Matrix.trace _
    rw [← Matrix.trace_conjTranspose,
      (Matrix.isHermitian_conjTranspose_mul_self (fullFock state * coordinates state)).eq]
  have squareReal : square.im = 0 := Complex.conj_eq_iff_im.mp squareStar
  have contraction : Matrix.trace (state.occupied.conjTranspose * rawFock state * direction) =
      -Complex.I * square := by
    dsimp only [direction, square]
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    rw [← Matrix.mul_assoc, frame]
    simp only [Matrix.conjTranspose_mul, (full_fock_hermitian state).eq, Matrix.mul_assoc]
  have zeroRate : Polynomial.occupiedDifferential (rawCore state) (rawTensor state) state.occupied direction = 0 := by
    rw [evaluation, contraction]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      squareReal, neg_zero, zero_mul, mul_zero, sub_self]
  change HasDerivAt (fun time : ℝ => (response state time).energy)
    (Polynomial.occupiedDifferential (rawCore state) (rawTensor state) state.occupied direction) 0 at actual
  rw [zeroRate] at actual
  exact actual

end
end CPS1ReactiveFieldDynamics
