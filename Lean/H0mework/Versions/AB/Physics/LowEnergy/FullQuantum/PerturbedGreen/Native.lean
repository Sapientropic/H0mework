import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialGreen.Integral
import H0mework.Versions.AB.Physics.LowEnergyResponse.Yukawa

/-! Primitive gauge and scalar variations generate the complete Dirac perturbation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity StageNineCurrentCoframeMatterTemporalPrincipal
open SU7MotherLieAlgebra SU7MotherGaugeTheory Triangular
open StageNineDiracDualFormNativeConjugateMatterVariation
noncomputable section

def varied (C : StageNineHolonomicConfiguration) (gauge : BasePoint → P286GaugeOneForm)
    (scalar : BasePoint → ScalarCoordinateCarrier) (epsilon : ℝ) : StageNineHolonomicConfiguration :=
  { varyP286GaugeConnectionCoordinate C gauge epsilon with
    scalar := fun p => C.scalar p+(epsilon : ℂ) • scalar p }

def insertion (C : StageNineHolonomicConfiguration) (gauge : BasePoint → P286GaugeOneForm)
    (scalar : BasePoint → ScalarCoordinateCarrier) (point : BasePoint) : Mother :=
  YangMills.Response.Forcing.spatialInsertion C gauge point+
    (currentCoframeMatterTemporalPrincipal (C.coframe point)).comp
      (diracExteriorMotherLieAction (p286GaugeConnectionMotherVariation gauge point 0))+
    diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalar point))

theorem varied_connection (C : StageNineHolonomicConfiguration) (gauge : BasePoint → P286GaugeOneForm)
    (scalar : BasePoint → ScalarCoordinateCarrier) (epsilon : ℝ) (point : BasePoint) (mu : LorentzianIndex) :
    connection (varied C gauge scalar epsilon) point mu=connection C point mu+
      (epsilon : ℂ) • diracExteriorMotherLieAction (p286GaugeConnectionMotherVariation gauge point mu) := by
  change connection (varyP286GaugeConnectionCoordinate C gauge epsilon) point mu=_
  unfold connection
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,p286LieBlockEmbed_add,
    p286LieBlockEmbed_real_smul,diracExteriorMotherLieAction_add,diracExteriorMotherLieAction_real_smul]
  simp only [p286GaugeConnectionMotherVariation]
  exact (add_assoc _ _ _).symm

theorem varied_diracKernel (C : StageNineHolonomicConfiguration) (gauge : BasePoint → P286GaugeOneForm)
    (scalar : BasePoint → ScalarCoordinateCarrier) (epsilon : ℝ) (point : BasePoint)
    (momentum : Fin 3 → ℝ) (z : ℂ) :
    diracKernel (varied C gauge scalar epsilon) point momentum z=
      diracKernel C point momentum z+(epsilon : ℂ) • insertion C gauge scalar point := by
  apply LinearMap.ext
  intro v
  have coframe : (varied C gauge scalar epsilon).coframe=C.coframe := rfl
  have value : (varied C gauge scalar epsilon).scalar point=C.scalar point+(epsilon : ℂ) • scalar point := rfl
  simp only [diracKernel,lowerSymbol,knownSymbol,coframe,value,varied_connection,
    map_add,map_smul,diracDualRightChiralYukawaAction_add,diracDualRightChiralYukawaAction_smul,
    insertion,YangMills.Response.Forcing.spatialInsertion,LinearMap.add_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply,map_add,map_smul,
    Finset.sum_add_distrib,Finset.smul_sum,smul_add,smul_smul]
  rw [mul_comm Complex.I (epsilon : ℂ)]
  abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
