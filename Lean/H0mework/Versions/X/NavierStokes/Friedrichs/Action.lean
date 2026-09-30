import H0mework.Versions.X.NavierStokes.Friedrichs.Principal

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsAction

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField StageNineDiracMatterCoordinateCalculus
open StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeCanonicalFluidCoframe NativeMaterialJetAction NativeSourceMaterialAdjoint
open NativeCanonicalFriedrichsPrincipal NativePauliCoframeAction NativePauliMotherAction

noncomputable section

attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

theorem frame_spin (direction : Fin 4) :
    diracFrameEvolutionPrincipal direction = spinActionMatrix direction := by
  fin_cases direction
  · exact diracFrameEvolutionPrincipal_time_eq_one
  all_goals simp [diracFrameEvolutionPrincipal, diracFramePrincipal,
    smul_smul, Complex.I_mul_I, spinActionMatrix]

theorem normalized_spin (velocity : PhysicalSpace) (direction : Fin 4) :
    normalized velocity direction =
      ((compensation velocity direction)⁻¹ : ℂ) • spinActionMatrix direction := by
  induction direction using Fin.cases with
  | zero => simp [normalized_time, compensation, spinActionMatrix]
  | succ direction =>
    rw [normalized_spatial, frame_spin]
    simp [compensation]

def kinetic (velocity : PhysicalSpace) (jet : Fin 4 → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  ∑ direction, diracMatrixMatterAction (normalized velocity direction) (jet direction)

theorem kinetic_original (velocity : PhysicalSpace) (jet : Fin 4 → DiracExteriorMatterCarrier) :
    kinetic velocity jet = currentCoframeMatterTemporalPrincipalInverse (coframe velocity)
      (gaugeVectorAt (coframe velocity) jet) := by
  rw [actual_derivative_inverse]
  simp only [kinetic, normalized_spin, diracMatrixMatterAction_smul_matrix, normalizedDerivative]

/-- The original Cartan, constitutive, and jet-generated color operators all remain here. -/
def lower (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction, (diracMatrixMatterAction (normalized velocity direction)).comp
    (NativeBalancedMaterialJet.connectionOperator velocity jet direction)

def action (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    DiracExteriorMatterCarrier :=
  kinetic velocity (rawDerivative jet) + lower velocity jet (matter velocity)

theorem action_firstJet (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    action velocity jet = kinetic velocity (NativeBalancedMaterialJet.derivative velocity jet) := by
  simp only [action, kinetic, lower, LinearMap.sum_apply, LinearMap.comp_apply,
    NativeBalancedMaterialJet.derivative, map_add, Finset.sum_add_distrib]

theorem action_original (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    action velocity jet = currentCoframeMatterTemporalPrincipalInverse (coframe velocity)
      (gaugeVectorAt (coframe velocity) (NativeBalancedMaterialJet.derivative velocity jet)) := by
  rw [action_firstJet, kinetic_original]

/-- The complete source connection consumes the same original first jet. -/
theorem action_divergence (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    action velocity jet =
      (density velocity * ∑ direction : Fin 3, normalizedJet jet direction.succ direction : ℂ) •
        lowerMatter 1 := by
  rw [action_original, NativeBalancedMaterialJet.primalVector_eq]
  have source : gaugeVectorAt (coframe velocity) (NativeConstitutiveJet.derivative velocity jet) =
      gaugeVectorAt (coframe velocity) (covariantDerivative velocity jet) := by
    simp only [NativeConstitutiveJet.derivative_split, gaugeVectorAt, map_add,
      Finset.sum_add_distrib, smul_add]
    change gaugeVectorAt (coframe velocity) (covariantDerivative velocity jet) +
      gaugeVectorAt (coframe velocity) (NativeConstitutiveFlux.increment velocity) = _
    rw [NativeConstitutiveFlux.vector_zero, add_zero]
    rfl
  rw [source, NativeMaterialJetAction.actual_inverse_response]

theorem raw_time (jet : Fin 4 → PhysicalSpace) (velocity : PhysicalSpace) :
    kinetic velocity (rawDerivative jet) = rawDerivative jet 0 +
      ∑ direction : Fin 3, (density velocity : ℂ) •
        diracMatrixMatterAction (diracFrameEvolutionPrincipal direction.succ)
          (rawDerivative jet direction.succ) := by
  rw [kinetic, Fin.sum_univ_succ]
  simp only [normalized_time, normalized_spatial, diracMatrixMatterAction_smul_matrix]
  congr 1
  funext spin
  simp [diracMatrixMatterAction, Matrix.one_apply]

/-- The generated normalized coefficients expose their exact ordinary first derivative. -/
theorem spatial_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    {tangent : PhysicalSpace} (actual : HasDerivAt path tangent time) (direction : Fin 3) :
    HasDerivAt (fun t => normalized (path t) direction.succ)
      ((inner ℝ (path time) tangent / 4 : ℝ) • diracFrameEvolutionPrincipal direction.succ) time := by
  have scalar : HasDerivAt (fun t => density (path t))
      (inner ℝ (path time) tangent / 4) time := by
    convert! (actual.norm_sq.div_const 8).const_add 2 using 1
    ring
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  simpa only [normalized_spatial, Matrix.smul_apply, Complex.real_smul, smul_eq_mul] using
    scalar.smul_const (diracFrameEvolutionPrincipal direction.succ row column)

end
end SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsAction
