import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Independent
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Source
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Pair

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ContinuousGradient

def primitiveReal (centre : Point) (mode : Nat) (jet : MultiIndex) (x : Point) : ℝ :=
  SourceGaussianModel.orbital [primitive mode] jet (x-centre)

def primitiveEnvelope (mode : Nat) (jet : MultiIndex) : ℝ :=
  GlobalSource.orbitalBound [primitive mode] jet

theorem primitive_real_integrable (centre : Point) (mode : Nat) (jet : MultiIndex) :
    Integrable (primitiveReal centre mode jet) (volume : Measure Point) :=
  (GlobalSource.orbital_integrable [primitive mode] (primitive_positive mode) jet).comp_sub_right centre

theorem primitive_real_continuous (centre : Point) (mode : Nat) (jet : MultiIndex) :
    Continuous (primitiveReal centre mode jet) :=
  (SourceGaussianModel.orbital_contDiff [primitive mode] jet 0).continuous.comp
    (continuous_id.sub continuous_const)

theorem primitive_real_bound (centre : Point) (mode : Nat) (jet : MultiIndex) (x : Point) :
    ‖primitiveReal centre mode jet x‖ ≤ primitiveEnvelope mode jet := by
  simpa only [primitiveReal,primitiveEnvelope,Real.norm_eq_abs] using
    GlobalSource.orbital_uniform_bound [primitive mode] (primitive_positive mode) jet (x-centre)

theorem primitive_real_product_integrable (centre : Point) (i j : Nat) (jetI jetJ : MultiIndex) :
    Integrable (fun x : Point => primitiveReal centre i jetI x * primitiveReal centre j jetJ x)
      (volume : Measure Point) :=
  (primitive_real_integrable centre j jetJ).bdd_mul
    (primitive_real_continuous centre i jetI).aestronglyMeasurable
    (Filter.Eventually.of_forall (primitive_real_bound centre i jetI))

theorem primitive_real_product_bound (centre : Point) (i j : Nat) (jetI jetJ : MultiIndex) (x : Point) :
    ‖primitiveReal centre i jetI x * primitiveReal centre j jetJ x‖ ≤
      primitiveEnvelope i jetI * primitiveEnvelope j jetJ := by
  rw [norm_mul]
  exact mul_le_mul (primitive_real_bound centre i jetI x) (primitive_real_bound centre j jetJ x)
    (norm_nonneg _) ((norm_nonneg _).trans (primitive_real_bound centre i jetI x))

theorem primitive_nuclear_integrable (centre : Point) (i j : Nat) (nuclear : Point)
    (jetI jetJ : MultiIndex) :
    Integrable (fun x : Point => SourceCoulomb.kernel (x-nuclear) •
      (star (orbitalValue centre i jetI x) * orbitalValue centre j jetJ x)) (volume : Measure Point) := by
  have actual := (SourceCoulomb.integrable_mul_shifted_kernel _
    (primitive_real_product_integrable centre i j jetI jetJ)
    (primitiveEnvelope i jetI * primitiveEnvelope j jetJ)
    (primitive_real_product_bound centre i j jetI jetJ) nuclear).ofReal (𝕜 := ℂ)
  convert! actual using 1
  funext x
  simp [orbitalValue,primitiveReal,Algebra.smul_def,mul_comm]

theorem coulomb_kernel_sub_comm (x y : Point) :
    SourceCoulomb.kernel (x-y) = SourceCoulomb.kernel (y-x) := by
  rw [← neg_sub x y]
  simp only [SourceCoulomb.kernel,SourceCoulomb.distance,Pi.neg_apply,neg_sq]

theorem primitive_pair_integrable (centre : Point) (i j k l : Nat) :
    Integrable (fun z : Point × Point =>
      (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
        star (orbitalValue centre i 0 z.1) * orbitalValue centre j 0 z.1 *
        star (orbitalValue centre k 0 z.2) * orbitalValue centre l 0 z.2)
      ((volume : Measure Point).prod volume) := by
  have actual := (SourceCoulomb.pair_integrable _ _
    (primitive_real_product_integrable centre i j 0 0)
    (primitive_real_product_integrable centre k l 0 0)
    (primitiveEnvelope k 0 * primitiveEnvelope l 0)
    (primitive_real_product_bound centre k l 0 0)).ofReal (𝕜 := ℂ)
  convert! actual using 1
  funext z
  rw [coulomb_kernel_sub_comm z.1 z.2]
  simp [orbitalValue,primitiveReal,mul_comm,mul_assoc]

end
end CPS1ElectronicSource
