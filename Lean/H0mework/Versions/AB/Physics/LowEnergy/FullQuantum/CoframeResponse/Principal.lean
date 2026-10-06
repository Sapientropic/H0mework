import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Boundary
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Differentiating the original temporal principal retains its ordered
on-shell term; inversion itself generates the derivative of the Hamiltonian. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal DiracExteriorMatterAction
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : NormedAlgebra ℝ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

abbrev timeSymbol (principal lower : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (-Complex.I) • (Ring.inverse principal*lower)

theorem inverse_parameter (principal : ℝ → Matrix ι ι ℂ) (dPrincipal : Matrix ι ι ℂ)
    (t : ℝ) (regular : IsUnit (principal t)) (derivative : HasDerivAt principal dPrincipal t) :
    HasDerivAt (fun epsilon => Ring.inverse (principal epsilon))
      (-(Ring.inverse (principal t)*dPrincipal*Ring.inverse (principal t))) t := by
  have inversion := hasFDerivAt_ringInverse (𝕜 := ℝ) regular.unit
  rw [regular.unit_spec] at inversion
  have generated := inversion.comp_hasDerivAt t derivative
  convert! generated using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
  rw [Ring.inverse_of_isUnit regular]

theorem timeSymbol_parameter (principal lower : ℝ → Matrix ι ι ℂ)
    (dPrincipal dLower : Matrix ι ι ℂ) (t : ℝ) (regular : IsUnit (principal t))
    (principalDerivative : HasDerivAt principal dPrincipal t)
    (lowerDerivative : HasDerivAt lower dLower t) :
    HasDerivAt (fun epsilon => timeSymbol (principal epsilon) (lower epsilon))
      (-(Ring.inverse (principal t)*dPrincipal*timeSymbol (principal t) (lower t))-
        Complex.I • (Ring.inverse (principal t)*dLower)) t := by
  have derivative := ((inverse_parameter principal dPrincipal t regular principalDerivative).mul
    lowerDerivative).const_smul (-Complex.I)
  convert! derivative using 1
  simp only [timeSymbol]
  rw [Matrix.mul_smul,smul_add,Matrix.neg_mul,smul_neg]
  simp only [Matrix.mul_assoc]
  module

theorem timeSymbol_on_shell (principal lower dPrincipal dLower : Matrix ι ι ℂ) :
    -(Ring.inverse principal*dPrincipal*timeSymbol principal lower)-
      Complex.I • (Ring.inverse principal*dLower)=
      (-Complex.I) • (Ring.inverse principal*(dLower-Complex.I • (dPrincipal*timeSymbol principal lower))) := by
  simp only [Matrix.mul_sub,Matrix.mul_smul,smul_sub,smul_smul,neg_smul,
    Matrix.mul_assoc]
  simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  module

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
