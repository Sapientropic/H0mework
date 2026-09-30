import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Source

/-! Independent bounded gauge and scalar directions generate a genuine primitive affine field family. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
local instance fieldGaugeModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance fieldGaugeCoordinateFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem gaugePotential_add (first second : GaugeProfile) :
    gaugePotential (first+second)=gaugePotential first+gaugePotential second := by
  simp only [gaugePotential,gaugeMatrixField,map_add]

theorem gaugePotential_real_smul (r : ℝ) (profile : GaugeProfile) :
    gaugePotential (r • profile)=(r : ℂ) • gaugePotential profile := by
  let multiply : Lp (α := Position) FiberOperators ⊤ volume →L[ℝ] SpatialOperators :=
    ((ContinuousLinearMap.id ℂ FiberOperators).holderL volume ⊤ 2 2).restrictScalars ℝ
  have mapped := (multiply.comp (gaugeMap.compLpL ⊤ volume)).map_smul r profile
  change gaugePotential (r • profile)=r • gaugePotential profile at mapped
  exact mapped.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) r (gaugePotential profile))

theorem scalarPotential_add (first second : ScalarProfile) :
    potential (first+second)=potential first+potential second := by
  simp only [potential,matrixField,map_add]

theorem scalarPotential_smul (c : ℂ) (profile : ScalarProfile) :
    potential (c • profile)=c • potential profile := by
  simp only [potential,matrixField,map_smul]

theorem rawGauge_add (first second : GaugeProfile) : rawGauge 0 (first+second)=rawGauge 0 first+rawGauge 0 second := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [rawGauge,gaugePotential_add,ContinuousLinearMap.comp_apply,smul_apply,add_apply,map_add,smul_add]

theorem rawGauge_real_smul (r : ℝ) (profile : GaugeProfile) : rawGauge 0 (r • profile)=(r : ℂ) • rawGauge 0 profile := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [rawGauge,gaugePotential_real_smul,ContinuousLinearMap.comp_apply,smul_apply,map_smul,smul_smul]
  rw [mul_comm Complex.I (r : ℂ)]

def variation (gauge : GaugeProfile) (scalar : ScalarProfile) : SpatialOperators := rawGauge 0 gauge+potential scalar

def family (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (epsilon : ℝ) : SpatialOperators :=
  fullG 0 energy damping positive (gauge+epsilon • direction) 1 (scalar+(epsilon : ℂ) • scalarDirection)

theorem originalKernel_affine (energy damping : ℝ) (gauge direction : GaugeProfile)
    (scalar scalarDirection : ScalarProfile) (epsilon : ℝ) (field : SpatialGreen.Domain 0 energy damping) :
    originalKernel 0 energy damping (gauge+epsilon • direction) 1 (scalar+(epsilon : ℂ) • scalarDirection) field=
      originalKernel 0 energy damping gauge 1 scalar field+(epsilon : ℂ) • variation direction scalarDirection field.val := by
  simp only [originalKernel,rawGauge_add,rawGauge_real_smul,scalarPotential_add,scalarPotential_smul,
    Complex.ofReal_one,one_smul,variation,add_apply,smul_apply,smul_add]
  abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
