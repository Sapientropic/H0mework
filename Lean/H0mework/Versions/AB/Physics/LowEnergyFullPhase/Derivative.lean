import H0mework.Versions.AB.Physics.LowEnergyFullPhase.Operator

/-! The actual holonomic derivative of the full graded phase, including its degree-six shift. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair StageNineHolonomicField
open DiracCliffordRepresentation DiracExteriorMatterAction
noncomputable section

abbrev Coefficients := Fin 2 → DiracSpinorIndex → ℂ

def coefficients (six other : DiracSpinorIndex → ℝ) (point : BasePoint) : Coefficients :=
  fun index spin => phase (if index = 0 then six spin else other spin) point

def coefficientVelocity (six other : DiracSpinorIndex → ℝ) (point : BasePoint) : Coefficients :=
  fun index spin => phase (if index = 0 then six spin else other spin) point *
    (((if index = 0 then six spin else other spin) : ℝ) : ℂ) * Complex.I

private def coordinateEvaluation (matter : DiracExteriorMatterCarrier) :
    Coefficients →ₗ[ℂ] MatterCoordinateCarrier where
  toFun values := matterCoordinateEquiv (fun spin =>
    (values 0 spin • (matter spin).1,values 1 spin • (matter spin).2.1,
      values 1 spin • (matter spin).2.2))
  map_add' := by
    intro first second
    rw [← map_add]
    congr 1
    funext spin
    simp [add_smul]
  map_smul' := by
    intro scalar values
    rw [← map_smul]
    congr 1
    funext spin
    simp [smul_smul]

theorem coefficients_derivative (six other : DiracSpinorIndex → ℝ) (point : BasePoint) :
    HasFDerivAt (coefficients six other)
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
        (coefficientVelocity six other point)) point := by
  apply hasFDerivAt_pi'.mpr
  intro index
  apply hasFDerivAt_pi'.mpr
  intro spin
  convert! phase_hasFDerivAt (if index = 0 then six spin else other spin) point using 1
  ext direction
  simp [coefficientVelocity,mul_assoc]

def phaseVelocity (six other : DiracSpinorIndex → ℝ) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier := fun spin =>
  (coefficientVelocity six other point 0 spin • (matter spin).1,
    coefficientVelocity six other point 1 spin • (matter spin).2.1,
    coefficientVelocity six other point 1 spin • (matter spin).2.2)

theorem phaseOperator_derivative (six other : DiracSpinorIndex → ℝ) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) (mu : LorentzianIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun p => matterCoordinateEquiv (phaseOperator six other p matter)) point mu) =
      if mu = 0 then phaseVelocity six other point matter else 0 := by
  have derivative := (coordinateEvaluation matter).restrictScalars ℝ |>.toContinuousLinearMap.hasFDerivAt
    |>.comp point (coefficients_derivative six other point)
  change HasFDerivAt (fun p => matterCoordinateEquiv (phaseOperator six other p matter)) _ point at derivative
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  by_cases temporal : mu = 0
  · subst mu
    simp [coordinateDirection,coordinateEvaluation]
    rfl
  · simp [coordinateDirection,temporal,Ne.symm temporal,coordinateEvaluation]
    rfl

def phaseGenerator : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction diracGammaFive + (2 : ℂ) • MixedSymbol.degreeSix

theorem primal_velocity (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    phaseVelocity sixPrimalRate otherRate point matter =
      primal point ((-Complex.I*(frequency : ℂ)) • phaseGenerator matter) := by
  funext spin
  fin_cases spin
  all_goals apply Prod.ext
  all_goals try apply Prod.ext
  all_goals simp [phaseVelocity,coefficientVelocity,sixPrimalRate,otherRate,primal,phaseOperator,
    phaseGenerator,MixedSymbol.degreeSix,diracMatrixMatterAction,diracGammaFive,
    Matrix.diagonal_apply,smul_smul]
  all_goals module

theorem kinetic_phase_term (point : BasePoint) (mu : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    dual point (Complex.I • diracMatrixMatterAction (diracGamma mu)
      (phaseVelocity sixPrimalRate otherRate point matter)) =
      (frequency : ℂ) • diracMatrixMatterAction (diracGamma mu) (phaseGenerator matter) := by
  rw [primal_velocity,map_smul,gamma_preserved,map_smul,smul_smul]
  congr 1
  simp [← mul_assoc]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
