import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.RootError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
noncomputable section

def registeredCoordinates : Matrix Basis Basis ℝ := CFC.sqrt actualGram

theorem frame_registered_coordinates (positive : actualGram.PosDef) :
    normalizedSourceFrame * registeredCoordinates = realInverse := by
  have unit : IsUnit (CFC.sqrt actualGram) :=
    (CFC.isUnit_sqrt_iff actualGram positive.posSemidef.nonneg).mpr positive.isUnit
  let := unit.invertible
  simp [normalizedSourceFrame,registeredCoordinates,metricCorrection,Matrix.mul_assoc]

/-- Original inverse-root coefficients and the exact spatial basis represent the same wave. -/
theorem registered_expansion_preserved (positive : actualGram.PosDef) (v : Basis → ℝ) (x : Point) :
    ∑ b : Basis, (registeredCoordinates *ᵥ v) b * normalizedOrbital b x =
      expansion (realInverse *ᵥ v) x := by
  rw [normalized_expansion,Matrix.mulVec_mulVec,frame_registered_coordinates positive]

def registeredComplexCoordinates : Matrix Basis Basis ℂ := complexMatrix registeredCoordinates

theorem registered_complex_frame (positive : actualGram.PosDef) :
    complexFrame * registeredComplexCoordinates = complexMatrix realInverse := by
  rw [complexFrame,registeredComplexCoordinates,← complexMatrix_mul,frame_registered_coordinates positive]

def registeredState (D : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  registeredComplexCoordinates * D * star registeredComplexCoordinates

def registeredAOState (D : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  complexMatrix realInverse * D * star (complexMatrix realInverse)

theorem registered_state_spatially_preserved (positive : actualGram.PosDef) (D : Matrix Basis Basis ℂ) :
    complexFrame * registeredState D * star complexFrame = registeredAOState D := by
  unfold registeredState registeredAOState
  calc
    _ = (complexFrame*registeredComplexCoordinates)*D*star (complexFrame*registeredComplexCoordinates) := by
      simp only [star_mul,Matrix.mul_assoc]
    _ = _ := by rw [registered_complex_frame positive]

theorem registered_state_error (positive : actualGram.PosDef) (D : Matrix Basis Basis ℂ) :
    ‖registeredState D-D‖ ≤ ‖complexMatrix actualGram-1‖*‖D‖*
      (2+‖complexMatrix actualGram-1‖) := by
  have rootError : ‖registeredComplexCoordinates-1‖ ≤ ‖complexMatrix actualGram-1‖ := source_root_error positive
  have bound : ‖registeredComplexCoordinates‖ ≤ 1+‖complexMatrix actualGram-1‖ := by
    calc
      _ = ‖(registeredComplexCoordinates-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖registeredComplexCoordinates-1‖+‖(1 : Matrix Basis Basis ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  have split : registeredState D-D = (registeredComplexCoordinates-1)*D*star registeredComplexCoordinates +
      D*star (registeredComplexCoordinates-1) := by
    unfold registeredState
    simp only [star_sub,star_one]
    noncomm_ring
  rw [split]
  calc
    _ ≤ ‖(registeredComplexCoordinates-1)*D*star registeredComplexCoordinates‖ +
      ‖D*star (registeredComplexCoordinates-1)‖ := norm_add_le _ _
    _ ≤ (‖registeredComplexCoordinates-1‖*‖D‖)*‖registeredComplexCoordinates‖ +
      ‖D‖*‖registeredComplexCoordinates-1‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (by rw [norm_star]; gcongr; exact norm_mul_le _ _)
      · simpa only [norm_star] using norm_mul_le D (star (registeredComplexCoordinates-1))
    _ ≤ (‖complexMatrix actualGram-1‖*‖D‖)*(1+‖complexMatrix actualGram-1‖)+
      ‖D‖*‖complexMatrix actualGram-1‖ := by gcongr
    _ = _ := by ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
