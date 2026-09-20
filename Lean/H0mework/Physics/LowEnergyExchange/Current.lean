import H0mework.Physics.LowEnergyQuantum.Carrier
import H0mework.Physics.LowEnergyEvolution.GaugeCurrent

/-! Full independent-dual source currents before any external-state restriction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Exchange
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineCoframeFirstJet
open StageNineP286GaugeConnectionVariation StageNineMatterVariation
open DiracCliffordRepresentation DiracExteriorMatterAction SU7MotherLieAlgebra
open StageNineDiracDualYukawaSpinJurisdiction StageNineDiracDualYukawaLocalSpinDensity
open SU7ExteriorBreakingYukawa
open StageNineDynamicBreakingVacuum StageNineDiracDualFormNativeConjugateMatterVariation
open scoped Matrix
noncomputable section

def currentOperator (coframe : LorentzianCoframe) (mu : LorentzianIndex)
    (matrix : P286LieBlockData) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • (diracMatrixMatterAction
    (inverseCoframeDiracGamma { coframe := coframe, derivative := 0 } mu)).comp
      (diracExteriorMotherLieAction (p286LieBlockEmbed matrix))

def current (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (mu : LorentzianIndex)
    (matrix : P286LieBlockData) : ℝ :=
  |coframe.det| * (dual (currentOperator coframe mu matrix matter)).re

theorem original_current (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : P286GaugeOneForm) :
    generatedVolumeDensity field * matterGaugeConnectionFirstVariationDensity
      positiveSmoothUnifiedSource 0 point field
        (pointwiseMatterP286GaugeConnectionVariation field variation) =
      ∑ mu, current field.coframe field.matter field.conjugateMatter mu
        (p286CoordinateEquiv.symm (variation mu)) := by
  unfold matterGaugeConnectionFirstVariationDensity matterGaugeConnectionVariationVector
    matterGaugeKineticSum pointwiseMatterP286GaugeConnectionVariation
    pointwiseP286GaugeConnectionMotherVariation current currentOperator
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    Finset.smul_sum, map_sum, Complex.re_sum, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Finset.mul_sum]
  rfl

theorem current_coordinates (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (mu : LorentzianIndex)
    (matrix : P286LieBlockData) :
    current coframe matter dual mu matrix = |coframe.det| *
      (∑ index, Quantum.dualCoordinates dual index *
        (Quantum.operatorMatrix (currentOperator coframe mu matrix) *ᵥ
          Quantum.coordinates matter) index).re := by
  unfold current
  rw [Quantum.full_response]

theorem current_quadratic (coframe : LorentzianCoframe)
    (matter perturbation : DiracExteriorMatterCarrier)
    (dual dualPerturbation : Module.Dual ℂ DiracExteriorMatterCarrier)
    (mu : LorentzianIndex) (matrix : P286LieBlockData) (parameter : ℝ) :
    current coframe (matter + parameter • perturbation) (dual + parameter • dualPerturbation) mu matrix =
      current coframe matter dual mu matrix + parameter *
        (current coframe matter dualPerturbation mu matrix + current coframe perturbation dual mu matrix) +
      parameter^2 * current coframe perturbation dualPerturbation mu matrix := by
  change current coframe (matter + (parameter : ℂ) • perturbation)
    (dual + (parameter : ℂ) • dualPerturbation) mu matrix = _
  simp only [current, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

def yukawaSource (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (scalar : ScalarCoordinateCarrier) : ℝ :=
  |coframe.det| * (dual (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar) matter)).re

theorem original_scalar_source (point : BasePoint) (field : StageNineContinuumPointField)
    (scalar : ScalarCoordinateCarrier) (parameter : ℝ) :
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      { field with scalar := field.scalar + (parameter : ℂ) • scalar } =
      generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point field +
        parameter * yukawaSource field.coframe field.matter field.conjugateMatter scalar := by
  simp only [generatedDensitizedContinuumDiracDualYukawaDensity, generatedContinuumDiracDualYukawaVector,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart,
    matterDualFrameRelative_zeroChart, map_add, map_smul, diracDualRightChiralYukawaAction_add,
    diracDualRightChiralYukawaAction_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, yukawaSource, generatedVolumeDensity]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Exchange
