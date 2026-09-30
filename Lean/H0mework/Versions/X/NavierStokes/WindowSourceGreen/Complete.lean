import H0mework.Versions.X.NavierStokes.WindowSourceGreen.TemporalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenCompleteForm
open MeasureTheory UnitAddTorus
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open PhysicsCore.DiracCliffordRepresentation
open NativeWindowGreenProduct NativeWindowGreenTestForm NativeWindowGreenTemporalForm
open NativeWindowGreenSourceForm (project physicalTest fullJet velocity)
open NativePhysicalFourier NativeCanonicalFluidCoframe
open NativeCanonicalGreenNormalization (densityJet)
noncomputable section
variable {nu : Viscosity}
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def operator : Fin 4 → SpinFiber G →L[ℂ] SpinFiber G := Fin.cases temporalOperator spatialOperator

theorem operator_norm (direction : Fin 4) : ‖operator (G := G) direction‖ ≤ 1 := by
  refine Fin.cases temporalOperator_norm (fun direction => spatialOperator_norm direction) direction

theorem operator_current (data : NativeStressPairingCarrier.Data) (direction : Fin 4)
    (first last : NativeHilbertDiracCurrent.Spinor data) :
    inner ℂ (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => first entry.1 entry.2))
      (operator direction (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => last entry.1 entry.2))) =
      NativeHilbertDiracCurrent.canonicalDual data first
        (NativeHilbertDiracCurrent.action data (Complex.I • diracGamma direction) last) := by
  refine Fin.cases (temporalOperator_current data first last)
    (fun direction => spatialOperator_current data direction first last) direction

def coefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) : Fin 4 → ComplexSpace :=
  Fin.cases (NativeWindowGreenTemporalCoefficient.coefficients seed time)
    (NativeWindowGreenSourceForm.coefficient seed time valid)

def coefficientBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  max (NativeWindowGreenTemporalForm.coefficientBudget seed)
    (NativeWindowGreenSourceForm.coefficientBudget seed horizon)

theorem coefficient_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (direction : Fin 4) : ‖coefficient seed time valid direction‖ ≤ coefficientBudget seed horizon := by
  refine Fin.cases ?_ (fun direction => ?_) direction
  · exact (NativeWindowGreenTemporalCoefficient.coefficients_bound seed time).trans (le_max_left _ _)
  · exact (NativeWindowGreenSourceForm.coefficient_bound seed time horizon valid before direction).trans (le_max_right _ _)

def remainder (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (T : Test (SpinFiber G)) : ℂ := ∑ direction : Fin 4, form (coefficient seed time valid direction) (operator direction) T

def formBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  nu.coeff*(2*Real.pi)^2+4*(Real.sqrt testKernel.cap*coefficientBudget seed horizon)^8*
    (nu.coeff*(2*Real.pi)^2/4)⁻¹^7

theorem remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (T : Test (SpinFiber G)) :
    ‖remainder seed time valid T‖ ≤ nu.coeff*((2*Real.pi)^2*gradient T)+formBudget seed horizon*‖decode T‖^2 := by
  let epsilon := nu.coeff*(2*Real.pi)^2/4
  have positive : 0 < epsilon := by dsimp only [epsilon]; positivity [nu.coeff_pos]
  have each (direction : Fin 4) : ‖form (coefficient seed time valid direction) (operator direction) T‖ ≤
      epsilon*gradient T+(epsilon+(Real.sqrt testKernel.cap*coefficientBudget seed horizon)^8*epsilon⁻¹^7)*‖decode T‖^2 := by
    have paid := form_absorption (coefficient seed time valid direction) (operator direction) T epsilon positive
    have controlled : ‖operator (G := G) direction‖*Real.sqrt testKernel.cap*‖coefficient seed time valid direction‖ ≤
        Real.sqrt testKernel.cap*coefficientBudget seed horizon := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (operator_norm direction)
        (Real.sqrt_nonneg _)) (norm_nonneg _)).trans
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left (coefficient_bound seed time horizon valid before direction) (Real.sqrt_nonneg testKernel.cap)
    apply paid.trans
    gcongr
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun direction _ => each direction)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at paid
  exact paid.trans_eq (by dsimp only [epsilon,formBudget]; ring)

def physicalCoefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Fin 4) (point : Torus) : ℂ :=
  ((densityJet (realValue (velocity seed time) point) (fullJet seed time valid point) direction /
    (if direction = 0 then density (realValue (velocity seed time) point) else 1) : ℝ) : ℂ)

theorem physical_test_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Fin 4) (F : Finset Wave) (T : Test (SpinFiber G)) :
    (∫ point : Torus, physicalCoefficient seed time valid direction point*
      inner ℂ (physicalTest F T point) (operator direction (physicalTest F T point))) =
        form (coefficient seed time valid direction) (operator direction) (project F T) := by
  refine Fin.cases ?_ (fun direction => ?_) direction
  · have same : (fun point : Torus => physicalCoefficient seed time valid 0 point*
        inner ℂ (physicalTest F T point) (operator 0 (physicalTest F T point))) =ᵐ[volume]
        (fun point : Torus => NativeWindowGreenTemporalCoefficient.sourceValue seed time point*
          inner ℂ (physicalTest F T point) (temporalOperator (physicalTest F T point))) := by
      filter_upwards [source_densityJet seed time valid] with point actual
      simp only [physicalCoefficient,operator,Fin.cases_zero,ite_true,actual]
    exact (integral_congr_ae same).trans (NativeWindowGreenTemporalForm.physical_test_integral seed time F T)
  · have same : (fun point : Torus => physicalCoefficient seed time valid direction.succ point*
        inner ℂ (physicalTest F T point) (operator direction.succ (physicalTest F T point))) =ᵐ[volume]
        (fun point : Torus => NativeWindowGreenSourceForm.physicalCoefficient seed time valid direction point*
          inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point))) := by
      filter_upwards [NativeWindowGreenSourceForm.physicalCoefficient_densityJet seed time valid direction] with point actual
      simp only [physicalCoefficient,operator,Fin.cases_succ,Fin.succ_ne_zero,if_false,div_one,actual]
    exact (integral_congr_ae same).trans (NativeWindowGreenSourceForm.physical_test_integral seed time valid direction F T)

theorem physical_remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (F : Finset Wave) (T : Test (SpinFiber G)) :
    ‖∑ direction : Fin 4, ∫ point : Torus, physicalCoefficient seed time valid direction point*
      inner ℂ (physicalTest F T point) (operator direction (physicalTest F T point))‖ ≤
      nu.coeff*((2*Real.pi)^2*gradient (project F T))+formBudget seed horizon*‖decode (project F T)‖^2 := by
  simp_rw [physical_test_integral]
  exact remainder_bound seed time horizon valid before (project F T)

theorem canonical_remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (F : Finset Wave)
    (T : Test (SpinFiber (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time)))) :
    ‖∑ direction : Fin 4, ∫ point : Torus, physicalCoefficient seed time valid direction point*
      NativeHilbertDiracCurrent.canonicalDual (NativeForwardWindowPairing.data seed time)
        (fun spin color => physicalTest F T point (spin,color))
        (NativeHilbertDiracCurrent.action (NativeForwardWindowPairing.data seed time) (Complex.I • diracGamma direction)
          (fun spin color => physicalTest F T point (spin,color)))‖ ≤
      nu.coeff*((2*Real.pi)^2*gradient (project F T))+formBudget seed horizon*‖decode (project F T)‖^2 := by
  have actual (direction : Fin 4) (point : Torus) := operator_current (NativeForwardWindowPairing.data seed time)
    direction (fun spin color => physicalTest F T point (spin,color)) (fun spin color => physicalTest F T point (spin,color))
  have same (field : SpinFiber (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time))) :
      WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => field (entry.1,entry.2)) = field := by
    ext entry
    rfl
  simp only [← actual,same]
  convert! physical_remainder_bound seed time horizon valid before F T using 1

theorem remainder_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time)
    (T : Test (SpinFiber G)) :
    remainder seed (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) T =
      remainder response.1 time (by linarith) T := by
  have same (direction : Fin 4) : coefficient seed (response.2.clockAdvance+time)
      (by linarith [response.2.clockAdvance_pos]) direction = coefficient response.1 time (by linarith) direction := by
    refine Fin.cases (NativeWindowGreenTemporalCoefficient.coefficients_next seed response generated time nonnegative)
      (fun direction => NativeWindowGreenSourceForm.coefficient_next seed response generated time nonnegative direction) direction
  simp only [remainder,same]

end
end SaturationMonoid.NavierStokes.NativeWindowGreenCompleteForm
