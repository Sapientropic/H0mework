import H0mework.NavierStokes.MaterialAction.MomentumJet

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeMaterialAdjointAction

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open StageNineFullDiracAdjointMaterial StageNineFullDiracAdjointLocalOperator
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliCoframeAction NativeMaterialJetAction NativeMaterialAdjointPrincipal NativeMaterialMomentumJet

noncomputable section

def gaugeOperator (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (NativePauliCoframeAction.connection velocity (target velocity derivative) direction))

theorem gauge_adjoint (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (gaugeOperator velocity derivative direction matter) candidate =
      -fullCanonicalDiracAdjoint matter (gaugeOperator velocity derivative direction candidate) := by
  exact LinearMap.congr_fun (fullCanonicalDiracAdjoint_motherLieConnection _ matter) candidate

theorem gauge_principal_commutes (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (candidate : DiracExteriorMatterCarrier) :
    principal velocity direction (gaugeOperator velocity derivative direction candidate) =
      gaugeOperator velocity derivative direction (principal velocity direction candidate) := by
  have commuting := LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal
    (inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction)
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed (NativePauliCoframeAction.connection velocity (target velocity derivative) direction)))) candidate
  simpa only [principal, gaugeOperator, diracExteriorMotherLieAction, LinearMap.smul_apply,
    map_smul, LinearMap.comp_apply] using congrArg (fun matter => Complex.I • matter) commuting

def primalKinetic (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (rawDerivative : Fin 4 → DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  ∑ direction, principal velocity direction
    (rawDerivative direction + spinOperator velocity derivative direction matter + gaugeOperator velocity derivative direction matter)

/-- Product rule for the actual density times inverse-coframe matter momentum. -/
def momentumDerivative (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (rawDerivative : Fin 4 → DiracExteriorMatterCarrier)
    (candidate : DiracExteriorMatterCarrier) (direction : Fin 4) : ℂ :=
  (coefficientDerivative velocity derivative direction : ℂ) * fullCanonicalDiracAdjoint matter
      (Complex.I • diracMatrixMatterAction (diracGamma direction) candidate) +
    (coefficient velocity direction : ℂ) * fullCanonicalDiracAdjoint (rawDerivative direction)
      (Complex.I • diracMatrixMatterAction (diracGamma direction) candidate)

def dualKinetic (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (rawDerivative : Fin 4 → DiracExteriorMatterCarrier)
    (candidate : DiracExteriorMatterCarrier) : ℂ :=
  (volumeFactor velocity : ℂ) * ∑ direction, fullCanonicalDiracAdjoint matter
    (principal velocity direction (spinOperator velocity derivative direction candidate + gaugeOperator velocity derivative direction candidate)) -
      ∑ direction, momentumDerivative velocity derivative matter rawDerivative candidate direction

private theorem adjoint_sum (matter : Fin 4 → DiracExteriorMatterCarrier) (candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (∑ direction, matter direction) candidate =
      ∑ direction, fullCanonicalDiracAdjoint (matter direction) candidate := by
  simp only [Fin.sum_univ_four, fullCanonicalDiracAdjoint_add, LinearMap.add_apply]

theorem primal_adjoint (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (rawDerivative : Fin 4 → DiracExteriorMatterCarrier)
    (candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (primalKinetic velocity derivative matter rawDerivative) candidate =
      -(∑ direction, fullCanonicalDiracAdjoint (rawDerivative direction) (principal velocity direction candidate)) +
        (∑ direction, fullCanonicalDiracAdjoint matter (spinOperator velocity derivative direction (principal velocity direction candidate))) +
        (∑ direction, fullCanonicalDiracAdjoint matter (gaugeOperator velocity derivative direction (principal velocity direction candidate))) := by
  simp only [primalKinetic, adjoint_sum, principal_adjoint, fullCanonicalDiracAdjoint_add,
    LinearMap.add_apply, spin_adjoint, gauge_adjoint, neg_add_rev, neg_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- The actual density derivative cancels the spin commutator on the complete canonical pairing. -/
theorem dual_eq_primal_adjoint (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (rawDerivative : Fin 4 → DiracExteriorMatterCarrier)
    (candidate : DiracExteriorMatterCarrier) :
    dualKinetic velocity derivative matter rawDerivative candidate =
      (volumeFactor velocity : ℂ) * fullCanonicalDiracAdjoint (primalKinetic velocity derivative matter rawDerivative) candidate := by
  have spinBalance := spin_commutator_pairing velocity derivative matter candidate
  simp only [map_sub, Finset.sum_sub_distrib] at spinBalance
  simp only [dualKinetic, momentumDerivative, map_add, Finset.sum_add_distrib,
    principal_divergence, ← weighted_principal, ← Finset.mul_sum, primal_adjoint,
    gauge_principal_commutes]
  linear_combination (volumeFactor velocity : ℂ) * spinBalance

end
end SaturationMonoid.NavierStokes.NativeMaterialAdjointAction
