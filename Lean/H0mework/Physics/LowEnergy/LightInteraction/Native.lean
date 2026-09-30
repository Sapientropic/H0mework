import H0mework.Physics.LowEnergyMatterSpace.GaugeCurrent
import H0mework.Physics.Coframe.CoframeVariation

/-! The original independent-dual current is polynomial in the coframe
adjugate. This retains the contact terms carried by the actual light legs. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineConnectionSectorSourceBalance StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineMatterVariation StageNineMatterCovariantDerivativeAffine
open SU7MotherLieAlgebra
noncomputable section

def adjugateCurrent (e : LorentzianCoframe)
    (data : LorentzianIndex → P286LieBlockData)
    (psi : DiracExteriorMatterCarrier) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  ∑ mu, ∑ a, e.adjugate mu a *
    (chi (Complex.I • diracMatrixMatterAction (diracGamma a)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (data mu)) psi))).re

private theorem dirac_sum (matrices : LorentzianIndex → DiracMatrix)
    (psi : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (∑ a, matrices a) psi=∑ a, diracMatrixMatterAction (matrices a) psi := by
  funext spin
  change (∑ column, (∑ a, matrices a spin column) • psi column)=
    ∑ a, ∑ column, matrices a spin column • psi column
  simp_rw [Finset.sum_smul]
  exact Finset.sum_comm

private theorem inverse_coefficient (e : LorentzianCoframe) (positive : 0<e.det)
    (mu a : LorentzianIndex) : e.det*e⁻¹ mu a=e.adjugate mu a := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ positive.ne',one_mul]

theorem original_current_adjugate (C : StageNineHolonomicConfiguration)
    (variation : P286GaugeOneForm) (point : BasePoint)
    (positive : 0<(C.coframe point).det) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource C variation point=
      adjugateCurrent (C.coframe point) (fun mu => p286CoordinateEquiv.symm (variation mu))
        (C.matter point) (C.conjugateMatter point) := by
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
  change |(C.coframe point).det| *(C.conjugateMatter point
    (Complex.I • ∑ mu, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := C.coframe point, derivative := 0 } mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation mu)))
        (C.matter point)))).re=_
  rw [abs_of_pos positive]
  simp only [inverseCoframeDiracGamma,dirac_sum,diracMatrixMatterAction_smul_matrix,
    Finset.smul_sum,map_sum,map_smul,smul_smul,smul_eq_mul,Complex.re_sum]
  unfold adjugateCurrent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm Complex.I ((C.coframe point)⁻¹ mu a : ℂ),mul_assoc,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [← mul_assoc,inverse_coefficient (C.coframe point) positive]
  simp only [map_smul,smul_eq_mul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
