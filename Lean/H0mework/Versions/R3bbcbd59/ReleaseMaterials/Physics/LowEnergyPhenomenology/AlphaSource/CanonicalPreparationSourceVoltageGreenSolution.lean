import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageGaussIdentity
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.PointSources

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumVoltageGaussGreen
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCanonicalCauchyState
open DiracExteriorMatterAction Stage9C.Material.SpinPair Stage10
open PreparationVacuumStaticVoltageSource SourcePropagationMotherEulerKernel
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb UnifiedAction
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap

/-- Response of the actual nine-group voltage family, on the original spatial coordinates at scale one. -/
def sourceVoltageTestResponse (test : 𝓢(Point, ℝ)) (point : Point) : ℝ :=
  deriv (fun a : ℝ=>nativeHolonomicEuler (sourceVoltageSignal (StaticGreen.sourceTest 1 test) a)
    (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) 20) 0

private theorem sourceTest_smooth (test : 𝓢(Point, ℝ)) : ContDiff ℝ ∞ (StaticGreen.sourceTest 1 test) :=
  test.smooth'.comp (StaticGreen.sourceSpatialMap 1).contDiff

/-- The original Green test operator and the full-action amplitude derivative are the same source response. -/
theorem sourceVoltage_test_generated (test : 𝓢(Point, ℝ)) (point : Point) :
    sourceVoltageTestResponse test point=StaticGreen.sourceEuler test point := by
  rw [sourceVoltageTestResponse,(sourceVoltage_Gauss_derivative _ (sourceTest_smooth test) _).deriv,
    StaticGreen.sourceEuler_laplacian,StaticGreen.sourceTest_laplacian,StaticGreen.slice_source_coordinates]
  simp

/-- The original heat-kernel fundamental solution acts on this actual field-response operator. -/
theorem sourceVoltage_green_fundamental (test : 𝓢(Point, ℝ)) :
    (∫ point : Point,StaticGreen.green point*sourceVoltageTestResponse test point)=test 0 := by
  simp only [sourceVoltage_test_generated]
  exact StaticGreen.green_original_euler test

/-- The source entering Gauss is the original charged current, with both physical legs retained. -/
def sourceVoltageRawCharge (matter : Point→DiracExteriorMatterCarrier)
    (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier) (point : Point) : ℝ :=
  (dual point (Stage9DEF.Compatibility.currentAction 0 HyperchargeResponse.chargeDirection (matter point))).re

/-- The generated Green potential solves the complete weak Gauss source equation for that same raw current. -/
theorem sourceVoltage_raw_potential (matter : Point→DiracExteriorMatterCarrier)
    (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier)
    (integrable : Integrable (sourceVoltageRawCharge matter dual)) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point,StaticGreen.potential (sourceVoltageRawCharge matter dual) point*
      sourceVoltageTestResponse test point)+
      (∫ point : Point,sourceVoltageRawCharge matter dual point*test point)=0 := by
  simp only [sourceVoltage_test_generated,StaticGreen.sourceEuler_laplacian]
  rw [StaticGreen.potential_weak_gauss _ integrable]
  ring

/-- Source-charge coefficients appear once in the original generated point-source Green potential. -/
theorem sourceVoltage_point_sources {count : ℕ} (positions : Fin count→Point) (charges : Fin count→ℝ)
    (test : 𝓢(Point, ℝ)) :
    (∫ point : Point,StaticGreen.pointSourcePotential positions charges point*sourceVoltageTestResponse test point)+
      ∑index,charges index*test (positions index)=0 := by
  simp only [sourceVoltage_test_generated]
  exact StaticGreen.pointSource_original_weak_gauss positions charges test

/-- The spatial coefficient is inherited from the original heat mass and the actual Gauss operator. -/
theorem sourceVoltage_potential_kernel (matter : Point→DiracExteriorMatterCarrier)
    (dual : Point→Module.Dual ℂ DiracExteriorMatterCarrier) (point : Point) :
    StaticGreen.potential (sourceVoltageRawCharge matter dual) point=
      -(∫ sourcePoint : Point,sourceVoltageRawCharge matter dual sourcePoint*
        kernel (point-sourcePoint)/(8*Real.pi*lapse)) := by
  simp only [StaticGreen.potential,StaticGreen.green_kernel,mul_div_assoc]

end LowEnergy.PreparationVacuumVoltageGaussGreen
