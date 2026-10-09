import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionSlice
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionIntegrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open UnifiedOrbitals
open scoped InnerProductSpace BigOperators
noncomputable section

theorem original_spatial_form_integrable (uTime : ℝ) (b c : Basis) (axis : Fin 3) :
    Integrable (fun x : Point => inner ℂ (sectionCovariant b 1 (spatialSlice uTime x) axis.succ)
      (sectionCovariant c 1 (spatialSlice uTime x) axis.succ)) := by
  simp_rw [spatial_section_form]
  exact (((source_product_integrable b c (raise zeroJet axis) (raise zeroJet axis)).ofReal.add
    ((source_product_integrable b c (raise zeroJet axis) zeroJet).ofReal.mul_const _)).add
    ((source_product_integrable b c zeroJet (raise zeroJet axis)).ofReal.mul_const _)).add
    ((source_product_integrable b c zeroJet zeroJet).ofReal.mul_const _)

def spatialCovariantForm (uTime : ℝ) (b c : Basis) : ℂ := (1/2 : ℂ) * ∑ axis : Fin 3,
  ∫ x : Point, inner ℂ (sectionCovariant b 1 (spatialSlice uTime x) axis.succ)
    (sectionCovariant c 1 (spatialSlice uTime x) axis.succ)

theorem original_spatial_form_integral (uTime : ℝ) (b c : Basis) (axis : Fin 3) :
    (∫ x : Point, inner ℂ (sectionCovariant b 1 (spatialSlice uTime x) axis.succ)
      (sectionCovariant c 1 (spatialSlice uTime x) axis.succ)) =
      (∫ x : Point, derivative b axis x * derivative c axis x : ℝ) +
      (firstDerivative axis c b : ℂ) * connectionPair (spatialSlice uTime 0) axis.succ +
      (firstDerivative axis b c : ℂ) * star (connectionPair (spatialSlice uTime 0) axis.succ) +
      (overlap b c : ℂ) * connectionSquare (spatialSlice uTime 0) axis.succ := by
  have h00 : Integrable (fun x : Point => ((ao b x * ao c x : ℝ) : ℂ)) :=
    (source_product_integrable b c zeroJet zeroJet).ofReal
  have h01 : Integrable (fun x : Point => ((ao b x * derivative c axis x : ℝ) : ℂ)) :=
    (source_product_integrable b c zeroJet (raise zeroJet axis)).ofReal
  have h10 : Integrable (fun x : Point => ((derivative b axis x * ao c x : ℝ) : ℂ)) :=
    (source_product_integrable b c (raise zeroJet axis) zeroJet).ofReal
  have h11 : Integrable (fun x : Point => ((derivative b axis x * derivative c axis x : ℝ) : ℂ)) :=
    (source_product_integrable b c (raise zeroJet axis) (raise zeroJet axis)).ofReal
  let a := connectionPair (spatialSlice uTime 0) axis.succ
  let d := connectionSquare (spatialSlice uTime 0) axis.succ
  simp_rw [spatial_section_form]
  have outer := integral_add ((h11.add (h10.mul_const a)).add (h01.mul_const (star a))) (h00.mul_const d)
  have middle := integral_add (h11.add (h10.mul_const a)) (h01.mul_const (star a))
  have first := integral_add h11 (h10.mul_const a)
  simp only [Pi.add_apply] at outer middle first
  rw [outer,middle,first]
  simp_rw [integral_mul_const,integral_complex_ofReal]
  have swapped : (∫ x : Point, derivative b axis x * ao c x) = firstDerivative axis c b := by
    unfold firstDerivative
    congr 1
    funext x
    exact mul_comm _ _
  rw [swapped]
  rfl

/-- The spatial quadratic form of the original U covariant derivative retains the AO kinetic term and exact connection corrections. -/
theorem original_spatial_form_decomposition (uTime : ℝ) (b c : Basis) :
    spatialCovariantForm uTime b c = (kinetic b c : ℂ) + (1/2 : ℂ) * ∑ axis : Fin 3,
      ((firstDerivative axis c b : ℂ)*connectionPair (spatialSlice uTime 0) axis.succ +
       (firstDerivative axis b c : ℂ)*star (connectionPair (spatialSlice uTime 0) axis.succ) +
       (overlap b c : ℂ)*connectionSquare (spatialSlice uTime 0) axis.succ) := by
  simp only [spatialCovariantForm,original_spatial_form_integral,kinetic,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_sum,Finset.sum_add_distrib,mul_add]
  ring

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
