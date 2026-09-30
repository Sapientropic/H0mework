import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.HeatDual
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorFiber

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalFourier
open NativeWindowHistoryCreationGeometry (transport square)
open NativeWindowHistoryHeatDual (energy energy_nonnegative)
open NativeWindowHistoryFrozenInverse (physical)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def response (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ)
    (x v : physicalSpace (modes M)) : physicalSpace (modes M) :=
  physical seed M sample (transport (modes M) (modes_zero M) (modes_closed M) nu v x)

theorem transport_skew (nu : Viscosity) (M : ℕ) (u v w : physicalSpace (modes M)) :
    pairing (modes M) w (transport (modes M) (modes_zero M) (modes_closed M) nu u v)=
      -pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu u w) := by
  have source:=NativeWindowOperatorGreen.convection_skew (modes M) (modes_zero M) (modes_closed M) nu
    (curlLift (modes M) u.1)
    (curlLift_reality (modes M) (modes_closed M) u.1 (physical_reality (fun {_} h => modes_closed M _ h) u)) v w
  change pairing (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u v) w=
    -pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu u w) at source
  rw [pairing_symmetric] at source
  exact source

theorem response_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ)
    (x v : physicalSpace (modes M)) :
    energy nu M (response seed M sample x v) ≤ nu.coeff⁻¹*
      (∫point : Torus,square (modes M) x point*square (modes M) v point) := by
  let y:=response seed M sample x v
  have original:=NativeWindowHistoryHeatDual.source_energy seed M sample
    (transport (modes M) (modes_zero M) (modes_closed M) nu v x)
  change energy nu M y=pairing (modes M) y (transport (modes M) (modes_zero M) (modes_closed M) nu v x) at original
  rw [transport_skew] at original
  have young:=NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M) (modes_closed M)
    nu v x y (-nu.coeff⁻¹)
  have scaled:=mul_le_mul_of_nonneg_left young nu.coeff_pos.le
  have inverse:nu.coeff*nu.coeff⁻¹=1:=mul_inv_cancel₀ nu.coeff_pos.ne'
  have same:(∫point : Torus,square (modes M) v point*square (modes M) x point)=
      ∫point : Torus,square (modes M) x point*square (modes M) v point := by
    congr 1
    funext point
    ring
  rw [same] at scaled
  have first:nu.coeff*(2*(-nu.coeff⁻¹)*pairing (modes M) x
      (transport (modes M) (modes_zero M) (modes_closed M) nu v y))=2*energy nu M y := by
    rw [original]
    calc
      _= -2*(nu.coeff*nu.coeff⁻¹)*pairing (modes M) x
        (transport (modes M) (modes_zero M) (modes_closed M) nu v y) := by ring
      _=_ := by rw [inverse]; ring
  have last:nu.coeff*((-nu.coeff⁻¹)^2*(∫point : Torus,square (modes M) x point*square (modes M) v point)+
      curlPair (modes M) y.1 y.1)=nu.coeff⁻¹*(∫point : Torus,square (modes M) x point*square (modes M) v point)+
        nu.coeff*curlPair (modes M) y.1 y.1 := by field_simp [nu.coeff_pos.ne']
  rw [first,last] at scaled
  have mass:=sq_nonneg ‖coefficients (modes M) y‖
  change energy nu M y≤_
  unfold energy at scaled ⊢
  linarith only [scaled,mass]

def budget (nu : Viscosity) (B epsilon : ℝ) : ℝ :=
  nu.coeff⁻¹*NativeWindowHistoryCreationForm.budget B (nu.coeff^2*epsilon*(2*Real.pi)^2)

theorem budget_nonnegative (nu : Viscosity) (B epsilon : ℝ) (positive : 0<epsilon) :
    0≤budget nu B epsilon := by
  unfold budget NativeWindowHistoryCreationForm.budget
  positivity [nu.coeff_pos]

theorem finite_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ)
    (x v : physicalSpace (modes M)) (B epsilon : ℝ) (positive : 0<epsilon)
    (bounded : ‖NativeWindowStressHeatSource.physical (square (modes M) x)‖≤B) :
    energy nu M (response seed M sample x v) ≤ epsilon*energy nu M v+
      budget nu B epsilon*‖coefficients (modes M) v‖^2 := by
  have scale:0<nu.coeff^2*epsilon := mul_pos (sq_pos_of_pos nu.coeff_pos) positive
  have absorbed:=NativeWindowHistoryCreationGeometry.square_absorption (square (modes M) x)
    (modes M) (modes_zero M) (modes_closed M) v (nu.coeff^2*epsilon) scale
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left bounded (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap:NativeWindowHistoryCreationForm.budget ‖NativeWindowStressHeatSource.physical (square (modes M) x)‖
      (nu.coeff^2*epsilon*(2*Real.pi)^2)≤NativeWindowHistoryCreationForm.budget B
        (nu.coeff^2*epsilon*(2*Real.pi)^2) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have mass:pairing (modes M) v v=‖coefficients (modes M) v‖^2 := real_inner_self_eq_norm_sq (coefficients (modes M) v)
  have paid:=(response_energy seed M sample x v).trans (mul_le_mul_of_nonneg_left
    (absorbed.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap (by rw [mass]; positivity))))
    (inv_nonneg.mpr nu.coeff_pos.le))
  rw [mass] at paid
  have same:nu.coeff⁻¹*(nu.coeff^2*epsilon*curlPair (modes M) v.1 v.1+
      NativeWindowHistoryCreationForm.budget B (nu.coeff^2*epsilon*(2*Real.pi)^2)*‖coefficients (modes M) v‖^2)=
        epsilon*nu.coeff*curlPair (modes M) v.1 v.1+budget nu B epsilon*‖coefficients (modes M) v‖^2 := by
    unfold budget
    field_simp [nu.coeff_pos.ne']
  rw [same] at paid
  have extra:=mul_nonneg positive.le (sq_nonneg ‖coefficients (modes M) v‖)
  unfold energy at paid ⊢
  linarith only [paid,extra]

theorem source_point_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ∀ᵐ lag ∂averageMeasure,∀ v : physicalSpace (modes M),
        energy nu M (response seed M (time-lag) (NativeWindowHistorySchurSampleControl.sample seed M time lag) v)≤
          epsilon*energy nu M v+C*‖coefficients (modes M) v‖^2 := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistorySchurAdvectorFiber.source_square_bound seed horizon nonnegative
  refine ⟨low,budget nu B epsilon,budget_nonnegative nu B epsilon positive,fun M above time inside => ?_⟩
  filter_upwards [source M above time inside] with lag bound
  exact fun v => finite_bound seed M (time-lag) _ v B epsilon positive bound

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianForm
