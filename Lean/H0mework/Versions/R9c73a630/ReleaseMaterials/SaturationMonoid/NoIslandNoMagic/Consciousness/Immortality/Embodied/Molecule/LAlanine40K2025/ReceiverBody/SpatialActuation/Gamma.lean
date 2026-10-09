import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Spatial

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb ContinuousGradient MeasureTheory
open UnifiedOrbitals
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem translation_measure_preserving :
    MeasurePreserving (fun x : Point => x-offset) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Point) (-offset)

def translationL2 : Lp ℝ 2 (volume : Measure Point) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure Point) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x-offset) translation_measure_preserving

theorem ao_memLp (i : Basis) : MemLp (ao i) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (orbital_contDiff (sourceTerms i) zeroJet 0).continuous.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs,sq_abs,pow_two,abs_mul_abs_self,ao] using source_product_integrable i i zeroJet zeroJet

theorem translated_ao_memLp (i : Basis) : MemLp (translatedAO i) 2 volume := by
  change MemLp (fun x => translatedAO i x) 2 volume
  simp_rw [ao_translation]
  exact (ao_memLp i).comp_measurePreserving translation_measure_preserving

def inputAOField (i : Basis) : Lp ℝ 2 (volume : Measure Point) := (ao_memLp i).toLp _
def generatedAOField (i : Basis) : Lp ℝ 2 (volume : Measure Point) := (translated_ao_memLp i).toLp _

theorem field_translation (i : Basis) : generatedAOField i=translationL2 (inputAOField i) := by
  apply Lp.ext
  have translated := (ao_memLp i).comp_measurePreserving translation_measure_preserving
  have actual := (translated_ao_memLp i).coeFn_toLp
  have transported := translated.coeFn_toLp
  change (generatedAOField i : Point → ℝ)=ᵐ[volume] translatedAO i at actual
  change (translationL2 (inputAOField i) : Point → ℝ)=ᵐ[volume] (fun x => ao i (x-offset)) at transported
  filter_upwards [actual,transported] with x left right
  rw [left]
  exact (ao_translation i x).trans right.symm

theorem field_norm_preserved (i : Basis) : ‖generatedAOField i‖=‖inputAOField i‖ := by
  rw [field_translation]
  exact translationL2.norm_map _

def originalKernel (D : Matrix Basis Basis ℂ) (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, Frame.registeredAOState D i j*(ao i x : ℂ)*(ao j y : ℂ)

def kernelFrom (D : Matrix Basis Basis ℂ) (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, Frame.registeredAOState D i j*(translatedAO i x : ℂ)*(translatedAO j y : ℂ)

def gammaKernel (x y : Point) : ℂ := kernelFrom generatedBody.realized x y

theorem kernel_translation (D : Matrix Basis Basis ℂ) (x y : Point) :
    kernelFrom D x y=originalKernel D (x-offset) (y-offset) := by
  simp only [kernelFrom,originalKernel,ao_translation]

theorem kernel_add (A B : Matrix Basis Basis ℂ) (x y : Point) :
    kernelFrom (A+B) x y=kernelFrom A x y+kernelFrom B x y := by
  simp only [kernelFrom,Frame.registeredAOState,Matrix.mul_add,
    Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem actual_gamma_translation (x y : Point) :
    gammaKernel x y=originalKernel input.body.realized (x-offset) (y-offset) :=
  kernel_translation input.body.realized x y

theorem full_gamma_residuals (x y : Point) : gammaKernel x y=
    kernelFrom input.body.held x y+kernelFrom input.body.inheritedResidual x y+
      kernelFrom input.body.newNumericalResidual x y := by
  change kernelFrom input.body.realized x y=_
  rw [FiniteContinuation.source_realization input input_admissible,kernel_add,kernel_add]

theorem gamma_diagonal_integral :
    (∫ x : Point, gammaKernel x x)=∫ x : Point, originalKernel input.body.realized x x := by
  simp_rw [actual_gamma_translation]
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => originalKernel input.body.realized x x) offset

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
