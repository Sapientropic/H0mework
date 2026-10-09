import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Gamma

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open UnifiedOrbitals
noncomputable section

-- These readers use the emitted body's coordinates and full matrix directly.
def offsetAt (body : ReceiverBody.Runtime.ActuationResult) (k : Fin 3) : ℚ :=
  body.frame.position 0 k-input.body.frame.position 0 k

def termAt (body : ReceiverBody.Runtime.ActuationResult) (term : Term) : Term :=
  { term with centre := fun k => term.centre k+offsetAt body k }

def termsAt (body : ReceiverBody.Runtime.ActuationResult) (i : Basis) : List Term :=
  (sourceTerms i).map (termAt body)

def aoAt (body : ReceiverBody.Runtime.ActuationResult) (i : Basis) (x : Point) : ℝ :=
  orbital (termsAt body i) zeroJet x

def gammaAt (body : ReceiverBody.Runtime.ActuationResult) (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, Frame.registeredAOState body.realized i j*(aoAt body i x : ℂ)*(aoAt body j y : ℂ)

theorem input_offset : offsetAt input.body=0 := by
  funext k
  simp only [offsetAt,sub_self,Pi.zero_apply]

theorem input_ao (i : Basis) (x : Point) : aoAt input.body i x=ao i x := by
  have terms : termAt input.body=id := by
    funext term
    simp only [termAt,input_offset,Pi.zero_apply,add_zero,id_eq]
  simp only [aoAt,termsAt,terms,List.map_id_fun,id_eq,ao]

theorem input_gamma (x y : Point) : gammaAt input.body x y=originalKernel input.body.realized x y := by
  simp only [gammaAt,input_ao,originalKernel]

theorem generated_offset : offsetAt generatedBody=offsetQ := by
  funext k
  simp only [offsetAt,generated_position,offsetQ,add_sub_cancel_left]

theorem generated_terms (i : Basis) : termsAt generatedBody i=translatedTerms i := by
  unfold termsAt translatedTerms
  congr 1
  funext term
  simp only [termAt,generated_offset,translatedTerm]

theorem generated_ao (i : Basis) (x : Point) : aoAt generatedBody i x=translatedAO i x := by
  rw [aoAt,generated_terms]
  rfl

theorem generated_gamma (x y : Point) : gammaAt generatedBody x y=gammaKernel x y := by
  simp only [gammaAt,generated_ao,gammaKernel,kernelFrom]

theorem current_frame_centres (i : Basis) : List.Forall (fun term =>
    ∃ a : Fin 13, term.centre=generatedBody.frame.position a) (termsAt generatedBody i) := by
  rw [generated_terms]
  exact translated_centres i

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
