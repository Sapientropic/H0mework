import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Scalar

/-! The history force is the primitive gauge and complete final scalar field of the original action. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen PerturbedGreen Triangular YangMills.FullPairing
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum DiracExteriorMatterAction
noncomputable section

def localForce (gauge : GaugeProfile) (epsilon : ℝ) (scalar : ScalarProfile) : SpatialOperators :=
  (-Complex.I*(epsilon : ℂ)) • gaugePotential gauge+scalarDriftMap scalar

theorem localForce_original (gauge : GaugeProfile) (epsilon : ℝ) (scalar : ScalarProfile) (field : FullMatterL2) :
    principal 0 (localForce gauge epsilon scalar field)=
      -(epsilon : ℂ) • rawGauge 0 gauge field-potential scalar field := by
  have temporalScalar : principal 0 (scalarDriftMap scalar field)= -potential scalar field := by
    rw [scalarDriftMap_apply,map_neg,inversePrincipal_right]
  simp only [localForce,add_apply,smul_apply,map_add,map_smul,temporalScalar,rawGauge,
    ContinuousLinearMap.comp_apply,smul_smul]
  module

theorem localForce_original_ae (gauge : GaugeProfile) (epsilon : ℝ) (scalar : ScalarProfile)
    (field : FullMatterL2) :
    principal 0 (localForce gauge epsilon scalar field)=ᵐ[volume] fun x =>
      -(epsilon : ℂ) • operator (PerturbedGreen.insertion actual (gaugeField gauge) (fun _ => 0)
        (spatialPoint x)) (field x)-
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalar x))) (field x) := by
  rw [localForce_original]
  filter_upwards [rawGauge_ae gauge field,potential_ae scalar field,
    Lp.coeFn_smul (-(epsilon : ℂ)) (rawGauge 0 gauge field),
    Lp.coeFn_sub (-(epsilon : ℂ) • rawGauge 0 gauge field) (potential scalar field)]
    with x gaugeRead scalarRead scaled subtracted
  simp only [Pi.smul_apply,Pi.sub_apply] at scaled subtracted
  rw [subtracted,scaled]
  rw [gaugeRead,scalarRead]

theorem primitive_kernel_difference (gauge : GaugeProfile) (epsilon : ℝ) (scalar : ScalarProfile)
    (k : Fin 3 → ℝ) (z : ℂ) (field : FullMatterL2) :
    (fun x => operator (diracKernel (GaugeGreen.configuration gauge epsilon scalar)
      (spatialPoint x) k z) (field x))=ᵐ[volume] fun x =>
      operator (diracKernel actual 0 k z) (field x)-backgroundY 0 field x-
        principal 0 (localForce gauge epsilon scalar field) x := by
  have generated := native_kernel_ae gauge epsilon scalar k z field
  have force := localForce_original gauge epsilon scalar field
  filter_upwards [generated,
    Lp.coeFn_smul (-(epsilon : ℂ)) (rawGauge 0 gauge field),
    Lp.coeFn_sub (-(epsilon : ℂ) • rawGauge 0 gauge field) (potential scalar field)]
    with x primitive scaled subtracted
  simp only [Pi.smul_apply,Pi.sub_apply] at scaled subtracted
  rw [primitive,force,subtracted,scaled]
  simp only [neg_smul]
  abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
