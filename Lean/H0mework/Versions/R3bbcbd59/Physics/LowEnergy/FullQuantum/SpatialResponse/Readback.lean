import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.SpatialResponse.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Original independent spatial duals consume the actual all-field response derivative in its ordered form. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section
attribute [local irreducible] fullG

def bilinearRead (dual source : FullMatterL2) : SpatialOperators →L[ℂ] ℂ :=
  (innerSL ℂ dual).comp (ContinuousLinearMap.apply ℂ FullMatterL2 source)

theorem bilinearRead_integral (dual source : FullMatterL2) (A : SpatialOperators) :
    bilinearRead dual source A=∫ x, inner ℂ (dual x) (A source x) := L2.inner_def _ _

theorem original_bilinear_derivative (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (dual source : FullMatterL2) :
    HasDerivAt (fun epsilon : ℝ => ∫ x, inner ℂ (dual x)
      (family energy damping positive gauge direction scalar scalarDirection epsilon source x))
      (-(∫ x, inner ℂ (dual x) (fullG 0 energy damping positive gauge 1 scalar
        (variation direction scalarDirection (fullG 0 energy damping positive gauge 1 scalar source)) x))) 0 := by
  have varied := ((bilinearRead dual source).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (family_derivative energy damping positive gauge direction scalar scalarDirection)
  convert! varied using 1
  change -(∫ x, inner ℂ (dual x) (fullG 0 energy damping positive gauge 1 scalar
    (variation direction scalarDirection (fullG 0 energy damping positive gauge 1 scalar source)) x))=
    bilinearRead dual source (-(fullG 0 energy damping positive gauge 1 scalar*variation direction scalarDirection*
      fullG 0 energy damping positive gauge 1 scalar))
  rw [map_neg,bilinearRead_integral]
  rfl

def twoLeg (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (reader : SpatialOperators)
    (epsilon : ℝ) : SpatialOperators :=
  family energy damping positive gauge direction scalar scalarDirection epsilon*reader*
    family energy damping positive gauge direction scalar scalarDirection epsilon

theorem twoLeg_derivative (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (reader : SpatialOperators) :
    let G := fullG 0 energy damping positive gauge 1 scalar
    let V := variation direction scalarDirection
    HasDerivAt (twoLeg energy damping positive gauge direction scalar scalarDirection reader)
      (-(G*V*G)*reader*G+G*reader*(-(G*V*G))) 0 := by
  dsimp only
  have derivative := family_derivative energy damping positive gauge direction scalar scalarDirection
  have twice := (derivative.mul_const reader).mul derivative
  simpa only [family_zero] using! twice

theorem independent_dual_twoLeg (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (reader : SpatialOperators)
    (epsilon : ℝ) (dual source : FullMatterL2) :
    inner ℂ ((family energy damping positive gauge direction scalar scalarDirection epsilon).adjoint dual)
      (reader (family energy damping positive gauge direction scalar scalarDirection epsilon source))=
      bilinearRead dual source (twoLeg energy damping positive gauge direction scalar scalarDirection reader epsilon) := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem independent_dual_equation (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (scalar : ScalarProfile) (dual : FullMatterL2)
    (field : SpatialGreen.Domain 0 energy damping) :
    inner ℂ ((fullG 0 energy damping positive gauge 1 scalar).adjoint dual)
      (originalKernel 0 energy damping gauge 1 scalar field)=inner ℂ dual field.val := by
  rw [ContinuousLinearMap.adjoint_inner_left,fullG_originalKernel]

theorem independent_current_derivative (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (reader : SpatialOperators)
    (dual source : FullMatterL2) :
    let G := fullG 0 energy damping positive gauge 1 scalar
    let V := variation direction scalarDirection
    HasDerivAt (fun epsilon : ℝ =>
      inner ℂ ((family energy damping positive gauge direction scalar scalarDirection epsilon).adjoint dual)
        (reader (family energy damping positive gauge direction scalar scalarDirection epsilon source)))
      (bilinearRead dual source (-(G*V*G)*reader*G+G*reader*(-(G*V*G)))) 0 := by
  dsimp only
  have derivative := ((bilinearRead dual source).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (twoLeg_derivative energy damping positive gauge direction scalar scalarDirection reader)
  simpa only [independent_dual_twoLeg] using! derivative

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
