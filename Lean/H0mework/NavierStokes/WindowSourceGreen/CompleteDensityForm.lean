import H0mework.NavierStokes.WindowSourceGreen.CompleteDensityCoefficient
import H0mework.NavierStokes.WindowSourceGreen.FormCritical

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowCompleteDensityForm
open Set Filter MeasureTheory
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeWindowGreenProduct NativeWindowGreenTestForm NativeWindowGreenCriticalForm
open NativeWindowCompleteDensityCoefficient (coefficient coefficientMap coefficientMap_bound cap cap_positive)
open NativeWindowSobolevStress (quarter quarter_nonnegative)
noncomputable section
universe u
variable {nu : Viscosity}

theorem source_high_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) (direction : Coordinate) (F : Finset Wave) :
    ‖high F (coefficient seed order time (by linarith [time.property.1]) direction)‖ ≤
      cap*‖NativeWindowSobolevUniformTail.high F (NativeWindowSobolevContinuity.curve seed order horizon time)‖ := by
  convert! coefficientMap_bound direction
    (NativeWindowSobolevUniformTail.high F (NativeWindowSobolevContinuity.curve seed order horizon time)) using 1
  rw [NativeWindowCompleteDensityCoefficient.map_high]
  rfl

def lowBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (F : Finset Wave) : ℝ :=
  (∑ k ∈ F, quarter k)*(cap*|NativeWindowSobolevStress.budget seed order horizon|)

theorem source_low_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) (direction : Coordinate) (F : Finset Wave) :
    ‖low F (coefficient seed order time (by linarith [time.property.1]) direction)‖ ≤ lowBudget seed order horizon F := by
  exact (low_norm F _).trans (mul_le_mul_of_nonneg_left
    (NativeWindowCompleteDensityCoefficient.source_bound seed order time horizon
      (by linarith [time.property.1]) time.property.2 direction)
    (Finset.sum_nonneg fun k _ => quarter_nonnegative k))

def remainder {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (T : Test (SpinFiber G)) : ℂ := ∑ direction : Coordinate,
  NativeWindowGreenCriticalForm.form (coefficient seed order time valid direction) (spatialOperator direction) T

theorem source_term_bound {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (time : Icc (0 : ℝ) horizon)
    (direction : Coordinate) (F : Finset Wave) (epsilon : ℝ) (positive : 0 < epsilon)
    (small : ‖spatialOperator (G := G) direction‖*Real.sqrt kernel.cap*
      ‖high F (coefficient seed order time (by linarith [time.property.1]) direction)‖ ≤ epsilon)
    (T : Test (SpinFiber G)) :
    ‖NativeWindowGreenCriticalForm.form (coefficient seed order time (by linarith [time.property.1]) direction)
      (spatialOperator direction) T‖ ≤ 2*epsilon*gradient T+
      (2*epsilon+(Real.sqrt testKernel.cap*lowBudget seed order horizon F)^8*epsilon⁻¹^7)*‖decode T‖^2 := by
  have paid := split_absorption (H := SpinFiber G) F (coefficient seed order time (by linarith [time.property.1]) direction)
    (spatialOperator direction) T epsilon positive (by convert! small using 1)
  have lower : ‖spatialOperator (G := G) direction‖*Real.sqrt testKernel.cap*
      ‖low F (coefficient seed order time (by linarith [time.property.1]) direction)‖ ≤
      Real.sqrt testKernel.cap*lowBudget seed order horizon F := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (spatialOperator_norm direction)
      (Real.sqrt_nonneg _)) (norm_nonneg _)).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_left
      (source_low_bound seed order horizon time direction F) (Real.sqrt_nonneg testKernel.cap)
  apply paid.trans
  gcongr

theorem exists_uniform_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (time : Icc (0 : ℝ) horizon) (G : Type u)
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (T : Test (SpinFiber G)),
      ‖remainder seed order time (by linarith [time.property.1]) T‖ ≤
        nu.coeff*((2*Real.pi)^2*gradient T)+C*‖decode T‖^2 := by
  let epsilon := nu.coeff*(2*Real.pi)^2/6
  have positive : 0 < epsilon := by dsimp only [epsilon]; positivity [nu.coeff_pos]
  let denominator := Real.sqrt kernel.cap*cap+1
  have denominator_pos : 0 < denominator := by dsimp only [denominator]; positivity [cap_positive]
  let delta := epsilon/denominator
  have delta_pos : 0 < delta := div_pos positive denominator_pos
  obtain ⟨F, tail⟩ := NativeWindowSobolevUniformTail.exists_uniform_high seed order horizon delta delta_pos
  let C := 3*(2*epsilon+(Real.sqrt testKernel.cap*lowBudget seed order horizon F)^8*epsilon⁻¹^7)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro time G _ _ _ T
  have small (direction : Coordinate) :
      ‖spatialOperator (G := G) direction‖*Real.sqrt kernel.cap*
        ‖high F (coefficient seed order time (by linarith [time.property.1]) direction)‖ ≤ epsilon := by
    have source := (source_high_bound seed order horizon time direction F).trans
      (mul_le_mul_of_nonneg_left (tail time).le cap_positive.le)
    apply (mul_le_mul (mul_le_mul_of_nonneg_right (spatialOperator_norm direction) (Real.sqrt_nonneg _))
      source (norm_nonneg _) (by positivity : 0 ≤ 1*Real.sqrt kernel.cap)).trans
    simp only [one_mul]
    have equal : (Real.sqrt kernel.cap*cap+1)*delta = epsilon := by
      dsimp only [delta,denominator]
      exact mul_div_cancel₀ _ denominator_pos.ne'
    nlinarith only [equal,delta_pos]
  have each (direction : Coordinate) := source_term_bound seed order horizon time direction F
    epsilon positive (small direction) T
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun direction _ => each direction)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at paid
  exact paid.trans_eq (by dsimp only [epsilon,C]; ring)

theorem current_integrand (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (T : Test (SpinFiber (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time))))
    (direction : Coordinate) (index : Wave × Wave) :
    NativeWindowGreenCriticalForm.integrand (coefficient seed 0 time valid direction) (spatialOperator direction) T index =
      NativePhysicalGradient.multiplier index.1 direction*
        NativePairedCurrentFourier.coefficient
          (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
          (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) 0 index.1*
        NativeHilbertDiracCurrent.canonicalDual (NativeForwardWindowPairing.data seed time)
          (fun spin color => decode T index.2 (spin,color))
          (NativeHilbertDiracCurrent.action (NativeForwardWindowPairing.data seed time)
            (Complex.I • PhysicsCore.DiracCliffordRepresentation.diracGamma direction.succ)
              (fun spin color => decode T (index.2-index.1) (spin,color))) := by
  exact congrArg₂ (fun first last : ℂ => first*last)
    (NativeWindowCompleteDensityCoefficient.current_row seed time valid direction index.1)
    (spatialOperator_current (NativeForwardWindowPairing.data seed time) direction
      (fun spin color => decode T index.2 (spin,color)) (fun spin color => decode T (index.2-index.1) (spin,color)))

theorem exists_canonical_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (time : Icc (0 : ℝ) horizon)
      (T : Test (SpinFiber (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time)))),
      ‖∑ direction : Coordinate, ∑' index : Wave × Wave,
        NativePhysicalGradient.multiplier index.1 direction*
          NativePairedCurrentFourier.coefficient
            (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
            (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) 0 index.1*
          NativeHilbertDiracCurrent.canonicalDual (NativeForwardWindowPairing.data seed time)
            (fun spin color => decode T index.2 (spin,color))
            (NativeHilbertDiracCurrent.action (NativeForwardWindowPairing.data seed time)
              (Complex.I • PhysicsCore.DiracCliffordRepresentation.diracGamma direction.succ)
                (fun spin color => decode T (index.2-index.1) (spin,color)))‖ ≤
        nu.coeff*((2*Real.pi)^2*gradient T)+C*‖decode T‖^2 := by
  obtain ⟨C,nonnegative,paid⟩ := exists_uniform_bound seed 0 horizon
  refine ⟨C,nonnegative,fun time T => ?_⟩
  have same := paid time (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time)) T
  simp only [remainder,NativeWindowGreenCriticalForm.form,current_integrand] at same
  convert! same using 1

theorem remainder_next {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time)
    (T : Test (SpinFiber G)) :
    remainder seed order (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) T =
      remainder response.1 order time (by linarith) T := by
  simp only [remainder,NativeWindowCompleteDensityCoefficient.coefficient_next seed order response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowCompleteDensityForm
