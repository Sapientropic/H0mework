import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GaugeLift
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureSynchronizedLocalActualLift

/-! Both original current legs are retained, including the independent dual. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation StageNineConnectionSectorSourceBalance
open StageNineGlobalIntegratedAction StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine Stage9C.Material.SpinPair
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open Stage9C.Dynamics.Homogeneous ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open scoped Matrix
noncomputable section

def tripletDualRead (dual : Module.Dual ℂ DiracExteriorMatterCarrier) : SourceIndex → ℂ :=
  fun index => dual (tripletLift (Pi.single index 1))

theorem tripletDualRead_apply (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : SourceIndex → ℂ) :
    dual (tripletLift v)=∑ index, tripletDualRead dual index*v index := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum,map_smul,smul_eq_mul,tripletDualRead]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

def tripletConfiguration (matter : BasePoint → SourceIndex → ℂ)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) : StageNineHolonomicConfiguration :=
  { actual with matter := fun point => tripletLift (matter point), conjugateMatter := dual }

theorem tripletConfiguration_current (matter : BasePoint → SourceIndex → ℂ)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (variation : P286GaugeOneForm) (point : BasePoint) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource (tripletConfiguration matter dual)
      variation point=
      lapse*(∑ index, tripletDualRead (dual point) index*
        (gaugeDiracMatrix (fun mu => p286CoordinateEquiv.symm (variation mu))*ᵥmatter point) index).re := by
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_chartZero,matterDerivativeFrameRelative_zeroChart]
  change |(actual.coframe point).det| * (dual point
    (Complex.I • ∑ mu, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } mu)
      (diracExteriorMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed
        (p286CoordinateEquiv.symm (variation mu))) (tripletLift (matter point))))).re=_
  simp_rw [← sourceInverseGamma_original point]
  rw [← gaugeDirac_original,tripletDualRead_apply,actual_coframe,homogeneousCoframe_det,
    abs_of_pos lapse_pos]

def gaugeCurrentValue (data : LorentzianIndex → SU7MotherLieAlgebra.P286LieBlockData)
    (v : SourceIndex → ℂ) (dual : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  lapse*(dual (tripletLift (gaugeDiracMatrix data*ᵥv))).re

theorem gaugeCurrent_quadratic (data : LorentzianIndex → SU7MotherLieAlgebra.P286LieBlockData)
    (background perturbation : SourceIndex → ℂ)
    (dual dualPerturbation : Module.Dual ℂ DiracExteriorMatterCarrier) (epsilon : ℝ) :
    gaugeCurrentValue data (background+(epsilon : ℂ) • perturbation)
      (dual+(epsilon : ℂ) • dualPerturbation)=
      gaugeCurrentValue data background dual+
        epsilon*(gaugeCurrentValue data background dualPerturbation+
          gaugeCurrentValue data perturbation dual)+
        epsilon^2*gaugeCurrentValue data perturbation dualPerturbation := by
  simp only [gaugeCurrentValue,Matrix.mulVec_add,Matrix.mulVec_smul,map_add,map_smul,
    LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
