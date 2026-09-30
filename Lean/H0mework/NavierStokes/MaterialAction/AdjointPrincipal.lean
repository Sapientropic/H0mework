import H0mework.NavierStokes.MaterialAction.SourceJet
import H0mework.Physics.Dirac.FullDiracAdjointLocalOperator

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeMaterialAdjointPrincipal

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineFullDiracAdjointMaterial StageNineFullDiracAdjointLocalOperator
open StageNineLorentzConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliCoframeAction NativeMaterialJetAction

noncomputable section

def principal (velocity : PhysicalSpace) (direction : Fin 4) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction
    (inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction)

theorem principal_gamma (velocity : PhysicalSpace) (direction : Fin 4) :
    principal velocity direction =
      (Complex.I * (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ)⁻¹) •
        diracMatrixMatterAction (diracGamma direction) := by
  apply LinearMap.ext
  intro matter
  simp only [principal, LinearMap.smul_apply, NativeCanonicalFluidCoframe.inverseGamma,
    RCLike.real_smul_eq_coe_smul (K := ℂ), diracMatrixMatterAction_smul_matrix, smul_smul]
  congr 2
  norm_cast

theorem principal_adjoint (velocity : PhysicalSpace) (direction : Fin 4)
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (principal velocity direction matter) candidate =
      -fullCanonicalDiracAdjoint matter (principal velocity direction candidate) := by
  rw [principal_gamma]
  simp only [LinearMap.smul_apply, fullCanonicalDiracAdjoint_smul,
    fullCanonicalDiracAdjoint_gamma, LinearMap.comp_apply, map_smul, smul_eq_mul]
  simp

def spinOperator (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (geometry velocity derivative).lorentzSpinConnection direction)

theorem spin_adjoint (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (spinOperator velocity derivative direction matter) candidate =
      -fullCanonicalDiracAdjoint matter (spinOperator velocity derivative direction candidate) := by
  exact LinearMap.congr_fun (fullCanonicalDiracAdjoint_spinConnection
    (geometry velocity derivative).lorentzSpinConnection direction matter) candidate

theorem spin_principal_reverse (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter
        (spinOperator velocity derivative direction (principal velocity direction candidate)) =
      fullCanonicalDiracAdjoint (principal velocity direction (spinOperator velocity derivative direction matter)) candidate := by
  rw [principal_adjoint, spin_adjoint, neg_neg]

theorem spin_kinetic (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) :
    (∑ direction, principal velocity direction (spinOperator velocity derivative direction matter)) =
      (-(3 / 2 : ℝ) * NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative) 0 : ℂ) •
        principal velocity 0 matter := by
  have actual := derivativeVector_eq_principal velocity
    (fun direction => spinOperator velocity derivative direction matter)
  rw [show (fun direction => spinOperator velocity derivative direction matter) =
      (fun direction => diracMatrixMatterAction (diracSpinConnectionLift
        (NativeCoframeSpin.jet velocity (NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative))).lorentzSpinConnection direction) matter) from rfl,
    NativeCoframeSpin.spin_response, map_smul] at actual
  simpa only [gaugeVectorAt, Finset.smul_sum, principal, spinOperator, geometry,
    currentCoframeMatterTemporalPrincipal, LinearMap.smul_apply] using actual

theorem spin_commutator_pairing (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter candidate : DiracExteriorMatterCarrier) :
    (∑ direction, fullCanonicalDiracAdjoint matter
      (principal velocity direction (spinOperator velocity derivative direction candidate) -
        spinOperator velocity derivative direction (principal velocity direction candidate))) =
      (-3 * NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative) 0 : ℂ) *
        fullCanonicalDiracAdjoint matter (principal velocity 0 candidate) := by
  simp only [map_sub, Finset.sum_sub_distrib, spin_principal_reverse]
  rw [← map_sum, spin_kinetic]
  have reversed : (∑ direction, fullCanonicalDiracAdjoint
      (principal velocity direction (spinOperator velocity derivative direction matter)) candidate) =
      fullCanonicalDiracAdjoint
        (∑ direction, principal velocity direction (spinOperator velocity derivative direction matter)) candidate := by
    simp only [Fin.sum_univ_four, fullCanonicalDiracAdjoint_add, LinearMap.add_apply]
  rw [reversed, spin_kinetic, map_smul, fullCanonicalDiracAdjoint_smul,
    LinearMap.smul_apply, principal_adjoint]
  simp [map_ofNat]
  ring

end
end SaturationMonoid.NavierStokes.NativeMaterialAdjointPrincipal
