import H0mework.Versions.R2.Physics.Material.CartanAssemblyQualification
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureSynchronizedLocalActualLift

/-! The exact source matter contact has one common null Clifford direction.
Every P286 action component has the same null current direction, so the
transverse one-dimensional attack retains the original source spinors. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalFiveSectorClosure
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineMatterCovariantDerivativeAffine
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

private abbrev Source := positiveSmoothUnifiedSource

def sourceNullClifford : DiracMatrix := diracGamma 0 - diracGamma 3

theorem sourceNullClifford_matter_zero :
    diracMatrixMatterAction sourceNullClifford diracSpinTwoMatterProbe = 0 := by
  funext spin
  fin_cases spin <;>
    simp [sourceNullClifford, diracMatrixMatterAction, diracGamma,
      diracGammaZero, diracGammaThree, diracSpinTwoMatterProbe, Fin.sum_univ_four]

theorem sourceNullClifford_dual_zero :
    diracSpinZeroMatterCoordinate.comp (diracMatrixMatterAction sourceNullClifford) = 0 := by
  apply LinearMap.ext
  intro matter
  simp [sourceNullClifford, diracMatrixMatterAction, diracGamma,
    diracGammaZero, diracGammaThree, diracSpinZeroMatterCoordinate, Fin.sum_univ_four]

/-- Internal mother action preserves the same kernel; the full P286 field
need not lie in a preselected Abelian block. -/
theorem sourceNullClifford_internalMatter_zero
    (generator : SU7MotherLieMatrix) :
    diracMatrixMatterAction sourceNullClifford
      (diracExteriorMotherLieAction generator diracSpinTwoMatterProbe) = 0 := by
  funext spin
  fin_cases spin <;>
    simp [sourceNullClifford, diracMatrixMatterAction, diracGamma,
      diracGammaZero, diracGammaThree, diracExteriorMotherLieAction,
      internalMatterLinearAction, diracSpinTwoMatterProbe, Fin.sum_univ_four]

theorem firstAssemblyCartanActual_matter_origin_null :
    diracMatrixMatterAction sourceNullClifford (firstAssemblyCartanActual.matter 0) = 0 := by
  have matter : firstAssemblyCartanActual.matter 0 = diracSpinTwoMatterProbe := by
    rw [firstAssemblyCartanActual_matter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe
  rw [matter]
  exact sourceNullClifford_matter_zero

theorem firstAssemblyCartanActual_dual_origin_null :
    (firstAssemblyCartanActual.conjugateMatter 0).comp
      (diracMatrixMatterAction sourceNullClifford) = 0 := by
  have dual : firstAssemblyCartanActual.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
    rw [firstAssemblyCartanActual_conjugateMatter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe
  rw [dual]
  exact sourceNullClifford_dual_zero

private theorem sourceMatterCurrent_single_normalForm
    (charge : P286CoordinateCarrier) (coordinate : LorentzianIndex) :
    p286MatterCurrentCoefficient Source firstAssemblyCartanActual
      (singleP286GaugeOneForm coordinate charge) 0 =
      if coordinate = 0 ∨ coordinate = 3 then
        (Complex.I * hyperchargeDegreeTwoMatterCoordinate
          (exteriorSpinorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm charge))
            p286HyperchargeMatterProbe)).re
      else 0 := by
  have coframe : firstAssemblyCartanActual.coframe 0 = 1 :=
    firstAssemblyCartanActual_coframe_origin_eq_safeFinal.trans
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe_origin_one
  have matter : firstAssemblyCartanActual.matter 0 = diracSpinTwoMatterProbe := by
    rw [firstAssemblyCartanActual_matter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe
  have dual : firstAssemblyCartanActual.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
    rw [firstAssemblyCartanActual_conjugateMatter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe
  have variation (direction : LorentzianIndex) :
      holonomicMatterGaugeConnectionVariation firstAssemblyCartanActual
        (fun _ => singleP286GaugeOneForm coordinate charge) 0 direction =
      if direction = coordinate then
        diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm charge))
          diracSpinTwoMatterProbe else 0 := by
    unfold holonomicMatterGaugeConnectionVariation p286GaugeConnectionMotherVariation
    rw [matter]
    by_cases same : direction = coordinate
    · subst direction
      simp only [singleP286GaugeOneForm, Pi.single_eq_same, ite_true]
    · simp only [singleP286GaugeOneForm, Pi.single_eq_of_ne same, map_zero,
        p286LieBlockEmbed_zero, if_neg same]
      exact diracExteriorMotherLieAction_zero_matrix _
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [toContinuumPointField, coframe, generatedVolumeDensity, Matrix.det_one,
    abs_one, one_mul, matterDualFrameRelative_chartZero, dual]
  simp only [matterDerivativeFrameRelative, matterFrameRelative_chartZero, variation]
  fin_cases coordinate <;>
    simp +decide [Fin.sum_univ_four, inverseCoframeDiracGamma,
      diracMatrixMatterAction, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, diracExteriorMotherLieAction,
      internalMatterLinearAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate]

theorem firstAssemblyCartanActual_allP286Current_nullRay
    (charge : P286CoordinateCarrier) (coordinate : LorentzianIndex) :
    p286MatterCurrentCoefficient Source firstAssemblyCartanActual
      (singleP286GaugeOneForm coordinate charge) 0 =
      if coordinate = 0 ∨ coordinate = 3 then
        p286MatterCurrentCoefficient Source firstAssemblyCartanActual
          (p286TemporalGaugeOneForm charge) 0
      else 0 := by
  have temporal := sourceMatterCurrent_single_normalForm charge (0 : LorentzianIndex)
  have directionEq : singleP286GaugeOneForm 0 charge = p286TemporalGaugeOneForm charge := by
    funext direction
    fin_cases direction <;> simp [singleP286GaugeOneForm, p286TemporalGaugeOneForm,
      canonicalLorentzianTimeDirection]
  rw [directionEq] at temporal
  simp only [true_or, ite_true] at temporal
  rw [sourceMatterCurrent_single_normalForm, temporal]

theorem firstAssemblyCartanActual_hyperchargeCurrent_fourVector
    (coordinate : LorentzianIndex) :
    p286MatterCurrentCoefficient Source firstAssemblyCartanActual
      (singleP286GaugeOneForm coordinate hyperchargeCoordinate) 0 =
      if coordinate = 0 ∨ coordinate = 3 then -1 else 0 := by
  rw [firstAssemblyCartanActual_allP286Current_nullRay,
    firstAssemblyCartanActual_temporalHyperchargeMatterCurrent]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
