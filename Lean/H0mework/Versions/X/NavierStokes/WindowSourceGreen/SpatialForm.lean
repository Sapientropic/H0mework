import H0mework.Versions.X.NavierStokes.SourcePairing.MotherTransportGreenNormalization
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.SpatialCoefficient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenSourceForm
open MeasureTheory UnitAddTorus
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowGreenProduct NativeEndpointVelocityCarrier NativeForwardWindowEvolution NativePhysicalFourier
open NativeWindowHistoryFirstJet
noncomputable section
variable {nu : Viscosity}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem velocity_reality (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (k : Wave) (coordinate : Coordinate) :
    velocity seed time (-k) coordinate = star (velocity seed time k coordinate) := by
  have original := congrFun (wholeVelocity_reality (NativeForwardWindowSource.source seed time).fst
    (NativeForwardWindowPairing.data seed time).reality k) coordinate
  change wholeVelocity (NativeForwardWindowSource.source seed time).fst (-k) coordinate =
    star (wholeVelocity (NativeForwardWindowSource.source seed time).fst k coordinate) at original
  simpa only [velocity,velocityJet,NativeForwardWindowJets.jet_zero] using! original

theorem physicalJet_real (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction coordinate : Coordinate) : ∀ᵐ point : Torus,
      (physicalJet seed time valid.le direction coordinate point).im = 0 := by
  apply NativeFourierReality.im_ae_zero_of_fourier_reality
  intro k
  have reality := velocity_reality seed time k coordinate
  simp only [velocity,velocityJet,NativeForwardWindowJets.jet_zero] at reality
  rw [physicalJet_fourier,physicalJet_fourier,NativeWindowHistoryTranslation.multiplier_neg,reality]
  simp [NativeSpatialTranslation.multiplier_eq]

def gradientValue (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) (point : Torus) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (physicalJet seed time valid.le direction coordinate point).re

def fullJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (point : Torus) : Fin 4 → PhysicalSpace :=
  Fin.cases (NativeCanonicalGreenNormalization.sourceField seed 1 time point)
    (fun direction => gradientValue seed time valid direction point)

theorem physicalCoefficient_densityJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) : ∀ᵐ point : Torus,
    physicalCoefficient seed time valid direction point =
      (NativeCanonicalGreenNormalization.densityJet (realValue (velocity seed time) point)
        (fullJet seed time valid point) direction.succ : ℂ) := by
  have first : ∀ coordinate : Coordinate, ∀ᵐ point : Torus, (scalarField (velocity seed time) coordinate point).im = 0 := by
    intro coordinate
    apply NativeFourierReality.im_ae_zero_of_fourier_reality
    intro k
    simpa only [scalarField_fourier,starRingEnd_apply] using! velocity_reality seed time k coordinate
  filter_upwards [ae_all_iff.mpr first,ae_all_iff.mpr (physicalJet_real seed time valid direction)] with point first last
  apply Complex.ext <;> simp [physicalCoefficient,NativeCanonicalGreenNormalization.densityJet,fullJet,
    realValue,gradientValue,PiLp.inner_apply,Complex.real_smul,first,last,mul_comm,div_eq_mul_inv]

open NativeWindowGreenTestForm
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def remainder (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (T : Test (SpinFiber G)) : ℂ := ∑ direction : Coordinate,
  form (coefficient seed time valid direction) (spatialOperator direction) T

def formBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  nu.coeff*(2*Real.pi)^2+3*(Real.sqrt testKernel.cap*coefficientBudget seed horizon)^8*
    (nu.coeff*(2*Real.pi)^2/3)⁻¹^7

theorem remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (T : Test (SpinFiber G)) :
    ‖remainder seed time valid T‖ ≤ nu.coeff*((2*Real.pi)^2*gradient T)+formBudget seed horizon*‖decode T‖^2 := by
  let epsilon := nu.coeff*(2*Real.pi)^2/3
  have positive : 0 < epsilon := by dsimp only [epsilon]; positivity [nu.coeff_pos]
  have each (direction : Coordinate) : ‖form (coefficient seed time valid direction) (spatialOperator direction) T‖ ≤
      epsilon*gradient T+(epsilon+(Real.sqrt testKernel.cap*coefficientBudget seed horizon)^8*epsilon⁻¹^7)*‖decode T‖^2 := by
    have paid := form_absorption (coefficient seed time valid direction) (spatialOperator direction) T epsilon positive
    have operator : ‖spatialOperator (G := G) direction‖*Real.sqrt testKernel.cap*‖coefficient seed time valid direction‖ ≤
        Real.sqrt testKernel.cap*coefficientBudget seed horizon := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (spatialOperator_norm direction) (Real.sqrt_nonneg _)) (norm_nonneg _)).trans
      simpa only [one_mul] using mul_le_mul_of_nonneg_left (coefficient_bound seed time horizon valid before direction) (Real.sqrt_nonneg testKernel.cap)
    apply paid.trans
    gcongr
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun direction _ => each direction)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at paid
  exact paid.trans_eq (by dsimp only [epsilon,formBudget]; ring)

theorem remainder_integrand_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (T : Test (SpinFiber (NativeStressPairingCarrier.Space (NativeForwardWindowPairing.data seed time))))
    (direction : Coordinate) (index : Wave × Wave) :
    integrand (coefficient seed time valid direction) (spatialOperator direction) T index =
      mFourierCoeff (physicalCoefficient seed time valid direction) index.1*
        NativeHilbertDiracCurrent.canonicalDual (NativeForwardWindowPairing.data seed time)
          (fun spin color => decode T index.2 (spin,color))
          (NativeHilbertDiracCurrent.action (NativeForwardWindowPairing.data seed time)
            (Complex.I • PhysicsCore.DiracCliffordRepresentation.diracGamma direction.succ)
              (fun spin color => decode T (index.2-index.1) (spin,color))) := by
  have current := spatialOperator_current (NativeForwardWindowPairing.data seed time) direction
    (fun spin color => decode T index.2 (spin,color)) (fun spin color => decode T (index.2-index.1) (spin,color))
  exact congrArg₂ (fun first last : ℂ => first*last) (coefficient_physical seed time valid direction index.1) current

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem coefficient_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction : Coordinate) :
    coefficient seed (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) direction =
      coefficient response.1 time (by linarith) direction := by
  apply lp.ext
  funext k
  simp only [coefficient_read,velocity,velocityJet,NativeForwardWindowJets.jet_next seed 0 response generated time nonnegative]

theorem remainder_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time)
    (T : Test (SpinFiber G)) :
    remainder seed (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) T =
      remainder response.1 time (by linarith) T := by
  simp only [remainder,coefficient_next seed response generated time nonnegative]

def project (F : Finset Wave) (T : Test (SpinFiber G)) : Test (SpinFiber G) := ∑ k ∈ F, lp.single 2 k (T k)

omit [CompleteSpace G] in
theorem project_read (F : Finset Wave) (T : Test (SpinFiber G)) (k : Wave) :
    decode (project F T) k = if k ∈ F then decode T k else 0 := by
  classical
  simp only [decode,project,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs <;> simp_all

def physicalTest (F : Finset Wave) (T : Test (SpinFiber G)) (point : Torus) : SpinFiber G :=
  ∑ k ∈ F, mFourier k point • decode T k

private def differenceEquiv : (Wave × Wave) ≃ (Wave × Wave) where
  toFun index := (index.1-index.2,index.1)
  invFun index := (index.2,index.2-index.1)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

omit [CompleteSpace G] in
theorem form_project (c : ComplexSpace) (A : SpinFiber G →L[ℂ] SpinFiber G) (F : Finset Wave) (T : Test (SpinFiber G)) :
    form c A (project F T) = ∑ p ∈ F, ∑ q ∈ F, c (p-q)*inner ℂ (decode T p) (A (decode T q)) := by
  classical
  have paid := differenceEquiv.summable_iff.mpr (form_summable c A (project F T)).of_norm
  rw [form,← differenceEquiv.tsum_eq]
  simp only [differenceEquiv,Equiv.coe_fn_mk,integrand,sub_sub_cancel]
  simp only [Function.comp_def,differenceEquiv,Equiv.coe_fn_mk,integrand,sub_sub_cancel] at paid
  rw [Summable.tsum_prod paid]
  rw [tsum_eq_sum (s := F) (fun p outside => by simp [project_read,if_neg outside])]
  apply Finset.sum_congr rfl
  intro p inside
  rw [tsum_eq_sum (s := F) (fun q outside => by simp [project_read,if_neg outside])]
  apply Finset.sum_congr rfl
  intro q included
  simp only [project_read,if_pos inside,if_pos included]

omit [CompleteSpace G] in
theorem physical_integral_of_coefficients (f : Torus → ℂ) (integrable : Integrable f) (c : ComplexSpace)
    (read : ∀ k, c k = mFourierCoeff f k) (A : SpinFiber G →L[ℂ] SpinFiber G)
    (F : Finset Wave) (T : Test (SpinFiber G)) :
    (∫ point : Torus, f point*inner ℂ (physicalTest F T point) (A (physicalTest F T point))) =
      form c A (project F T) := by
  have modulated (p q : Wave) : Integrable (fun point : Torus =>
      mFourier (-(p-q)) point*f point) :=
    integrable.bdd_mul (mFourier (-(p-q))).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun point => ((mFourier (-(p-q))).norm_coe_le_norm point).trans_eq mFourier_norm)
  have pointwise (point : Torus) : f point*
      inner ℂ (physicalTest F T point) (A (physicalTest F T point)) =
      ∑ p ∈ F, ∑ q ∈ F, (mFourier (-(p-q)) point*f point)*
        inner ℂ (decode T p) (A (decode T q)) := by
    simp only [physicalTest,map_sum,sum_inner,inner_sum,map_smul,inner_smul_left,inner_smul_right,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [← mFourier_neg]
    have phase : mFourier (-p) point*mFourier q point = mFourier (-(p-q)) point := by
      rw [← mFourier_add]
      congr 1
      abel_nf
    calc
      _ = (mFourier (-p) point*mFourier q point)*f point*
          inner ℂ (decode T p) (A (decode T q)) := by ring
      _ = _ := by rw [phase]
  simp_rw [pointwise]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (modulated p q).mul_const _)),form_project]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => (modulated p q).mul_const _)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_mul_const,read]
  rfl

theorem physical_test_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) (F : Finset Wave) (T : Test (SpinFiber G)) :
    (∫ point : Torus, physicalCoefficient seed time valid direction point*
      inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point))) =
        form (coefficient seed time valid direction) (spatialOperator direction) (project F T) :=
  physical_integral_of_coefficients _ (physicalCoefficient_integrable seed time valid direction) _
    (coefficient_physical seed time valid direction) _ F T

theorem physical_remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (F : Finset Wave) (T : Test (SpinFiber G)) :
    ‖∑ direction : Coordinate, ∫ point : Torus, physicalCoefficient seed time valid direction point*
      inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point))‖ ≤
      nu.coeff*((2*Real.pi)^2*gradient (project F T))+formBudget seed horizon*‖decode (project F T)‖^2 := by
  simp_rw [physical_test_integral]
  exact remainder_bound seed time horizon valid before (project F T)

theorem density_remainder_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (F : Finset Wave) (T : Test (SpinFiber G)) :
    ‖∑ direction : Coordinate, ∫ point : Torus,
      (NativeCanonicalGreenNormalization.densityJet (realValue (velocity seed time) point)
        (fullJet seed time valid point) direction.succ : ℂ)*
      inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point))‖ ≤
      nu.coeff*((2*Real.pi)^2*gradient (project F T))+formBudget seed horizon*‖decode (project F T)‖^2 := by
  have equal (direction : Coordinate) : (∫ point : Torus,
      (NativeCanonicalGreenNormalization.densityJet (realValue (velocity seed time) point)
        (fullJet seed time valid point) direction.succ : ℂ)*
      inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point))) =
      ∫ point : Torus, physicalCoefficient seed time valid direction point*
        inner ℂ (physicalTest F T point) (spatialOperator direction (physicalTest F T point)) := by
    apply integral_congr_ae
    filter_upwards [physicalCoefficient_densityJet seed time valid direction] with point actual
    rw [actual]
  simp_rw [equal]
  exact physical_remainder_bound seed time horizon valid before F T

end
end SaturationMonoid.NavierStokes.NativeWindowGreenSourceForm
