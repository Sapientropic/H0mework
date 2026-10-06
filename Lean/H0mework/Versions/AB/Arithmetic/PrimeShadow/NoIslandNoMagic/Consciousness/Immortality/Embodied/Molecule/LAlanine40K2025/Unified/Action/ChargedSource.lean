import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Classical
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionPreparations

/-! Original molecular D3 consumes a charge preparation of the complete U current. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.ChargedSource
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource Stage9DEF
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open YangMills.FullPairing Stage10.ChargedPreparation
open scoped InnerProductSpace
noncomputable section

def chargedSection (b : Basis) (scale : ℝ) (point : BasePoint) : Hilbert :=
  preparedSection preparation b scale point

theorem charge_pair (b c : Basis) (scale : ℝ) (point : BasePoint) :
    inner ℂ (chargedSection b scale point) (operator chargeMother (chargedSection c scale point)) =
      -(star (orbitalWeight b scale point) * orbitalWeight c scale point) := by
  simp only [chargedSection, preparedSection, map_smul, inner_smul_left, inner_smul_right,
    full_charge_pair]
  change orbitalWeight c scale point * (star (orbitalWeight b scale point) * (-1)) = _
  ring

def chargeDensity (scale : ℝ) (point : BasePoint) : ℂ :=
  ∑ b : Basis, ∑ c : Basis, (densityMatrix b c : ℂ) *
    inner ℂ (chargedSection b scale point) (operator chargeMother (chargedSection c scale point))

/-- The original D3 contraction retains its actual density, with the U-generated negative charge. -/
theorem original_D3_charge (scale : ℝ) (point : BasePoint) :
    chargeDensity scale point = -(sourceDensity (spatialPoint scale point) : ℂ) := by
  have same : chargeDensity scale point = -sectionDensity scale point := by
    simp only [chargeDensity, sectionDensity, scalarSection_pair, charge_pair,
      mul_neg, Finset.sum_neg_distrib]
  rw [same, original_D3_section_density]

theorem original_D3_charge_integrable (time : ℝ) :
    Integrable (fun x : Point => chargeDensity 1 (spatialSlice time x)) := by
  simp_rw [original_D3_charge, slice_coordinates]
  exact (GlobalSource.source_bilinear_integrable zeroJet zeroJet).ofReal.neg

theorem original_D3_total_charge (time : ℝ) :
    (∫ x : Point, chargeDensity 1 (spatialSlice time x)) =
      -((∫ x : Point, sourceDensity x : ℝ) : ℂ) := by
  simp_rw [original_D3_charge, slice_coordinates]
  rw [integral_neg, integral_complex_ofReal]

/-- The original classical current is tested by the original AO pair and contracted by original D3. -/
def classicalCurrentDensity (scale : ℝ) (point : BasePoint) : ℂ :=
  ∑ b : Basis, ∑ c : Basis, (densityMatrix b c : ℂ) *
    (star (orbitalWeight b scale point) * orbitalWeight c scale point *
      Stage9C.Material.SpinPair.actual.conjugateMatter point
        (dualPreparation (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
          (preparation (Stage9C.Material.SpinPair.actual.matter point)))))

theorem classical_D3_normalization (scale : ℝ) (point : BasePoint) :
    classicalCurrentDensity scale point =
      (4 * (Stage9C.Material.SpinPair.spinScale : ℂ)) * chargeDensity scale point := by
  simp only [classicalCurrentDensity, chargeDensity, classical_current, charge_pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem classical_D3_current (scale : ℝ) (point : BasePoint) :
    classicalCurrentDensity scale point = -4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
      (sourceDensity (spatialPoint scale point) : ℂ) := by
  rw [classical_D3_normalization, original_D3_charge]
  ring

end
end LAlanine40K2025.UnifiedAction.ChargedSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
