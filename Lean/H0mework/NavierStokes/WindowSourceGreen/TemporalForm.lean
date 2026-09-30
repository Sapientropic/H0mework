import H0mework.NavierStokes.WindowSourceGreen.TemporalCoefficient
import H0mework.NavierStokes.WindowSourceGreen.SpatialForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenTemporalForm
open MeasureTheory UnitAddTorus
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open NativeWindowGreenProduct NativeWindowGreenTestForm NativeWindowGreenTemporalCoefficient
open NativeWindowGreenSourceForm (project physicalTest physical_integral_of_coefficients fullJet)
open NativePhysicalFourier
open NativeCanonicalGreenNormalization (densityJet sourceField)
noncomputable section
variable {nu : Viscosity}
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def temporalOperator : SpinFiber G →L[ℂ] SpinFiber G :=
  (spinAction (G := G) diracAdjointSpinSwap).adjoint.comp (spinAction (Complex.I • diracGamma 0))

theorem temporalOperator_current (data : NativeStressPairingCarrier.Data)
    (first last : NativeHilbertDiracCurrent.Spinor data) :
    inner ℂ (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => first entry.1 entry.2))
      (temporalOperator (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => last entry.1 entry.2))) =
      NativeHilbertDiracCurrent.canonicalDual data first
        (NativeHilbertDiracCurrent.action data (Complex.I • diracGamma 0) last) := by
  rw [temporalOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply,Fintype.sum_prod_type]
  simp only [spinAction_apply,NativeHilbertDiracCurrent.canonicalDual,
    NativeHilbertDiracCurrent.action,LinearMap.coe_mk,AddHom.coe_mk]

omit [CompleteSpace G] in
theorem gamma_zero_norm (field : SpinFiber G) :
    ‖spinAction (Complex.I • diracGamma 0) field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,spinAction_apply]
  simp [diracGamma,diracGammaZero,Fin.sum_univ_four,Fin.sum_univ_two,norm_smul]
  ring

theorem temporalOperator_norm : ‖temporalOperator (G := G)‖ ≤ 1 := by
  have swap : ‖spinAction (G := G) diracAdjointSpinSwap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by rw [swap_norm,one_mul])
  have gamma : ‖spinAction (G := G) (Complex.I • diracGamma 0)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by rw [gamma_zero_norm,one_mul])
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact (mul_le_mul swap gamma (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

def coefficientBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  Real.sqrt 3*NativeForwardWindowJets.budget seed 1/4

theorem physical_test_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset Wave) (T : Test (SpinFiber G)) :
    (∫ point : Torus, sourceValue seed time point*
      inner ℂ (physicalTest F T point) (temporalOperator (physicalTest F T point))) =
        form (coefficients seed time) temporalOperator (project F T) := by
  have same : (∫ point : Torus, sourceValue seed time point*
      inner ℂ (physicalTest F T point) (temporalOperator (physicalTest F T point))) =
      ∫ point : Torus, field seed time point*
        inner ℂ (physicalTest F T point) (temporalOperator (physicalTest F T point)) := by
    apply integral_congr_ae
    filter_upwards [field_ae seed time] with point actual
    rw [actual]
  rw [same]
  exact physical_integral_of_coefficients _
    ((Lp.memLp (field seed time)).integrable (by norm_num)) _ (coefficients_read seed time) _ F T

theorem source_densityJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    ∀ᵐ point : Torus, sourceValue seed time point =
      ((densityJet (realValue (NativeWindowGreenSourceForm.velocity seed time) point)
        (fullJet seed time valid point) 0 /
          NativeCanonicalFluidCoframe.density (realValue (NativeWindowGreenSourceForm.velocity seed time) point) : ℝ) : ℂ) := by
  have original := realField_apply
    (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed 0 time))
  filter_upwards [original] with point actual
  have same : sourceField seed 0 time point =
      realValue (NativeWindowGreenSourceForm.velocity seed time) point := actual
  rw [← same]
  exact source_original seed time point (fullJet seed time valid point) rfl


end
end SaturationMonoid.NavierStokes.NativeWindowGreenTemporalForm
