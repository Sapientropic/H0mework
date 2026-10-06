import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Sections

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9DEF
open BasinRefinement SourceGaussianModel SourceFiniteData
open YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

def sectionAction (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) : Mother :=
  orbitalWeight b scale p • Compatibility.covariantAction direction +
    fieldDirectionalDerivative (orbitalWeight b scale) p direction • LinearMap.id

def sectionCovariant (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) : Hilbert :=
  operator (sectionAction b scale p direction) (prepared p)

theorem original_section_covariant (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    naturalCoordinates (holonomicMatterCovariantDerivative (orbitalTest b scale) p direction) =
      (2 : ℂ) • sectionCovariant b scale p direction := by
  have original : holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction =
      Compatibility.covariantAction direction (Stage10.Runtime.configuration.matter p) := by
    rw [Stage10.Runtime.configuration_eq]
    exact (Compatibility.actual_covariantAction p direction).symm
  rw [original_orbital_covariant,original]
  have action : orbitalWeight b scale p • Compatibility.covariantAction direction
        (Stage10.Runtime.configuration.matter p) +
      fieldDirectionalDerivative (orbitalWeight b scale) p direction • Stage10.Runtime.configuration.matter p =
        sectionAction b scale p direction (Stage10.Runtime.configuration.matter p) := rfl
  rw [action,← operator_coordinates,Stage10.Runtime.configuration_eq,actual_eq_twice_prepared,map_smul]
  rfl

theorem section_covariant_expansion (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    sectionCovariant b scale p direction =
      orbitalWeight b scale p • operator (Compatibility.covariantAction direction) (prepared p) +
        fieldDirectionalDerivative (orbitalWeight b scale) p direction • prepared p := by
  simp [sectionCovariant,sectionAction,operator]

/-- The original quantum response reads the full derivative pairing, after the source's one dual compensation. -/
theorem original_covariant_quantum_gram (b c : Basis) (scale : ℝ) (p : BasePoint)
    (direction : LorentzianIndex) :
    inner ℂ (sectionCovariant b scale p direction) (sectionCovariant c scale p direction) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer p)
        (Compatibility.responseMatrix (pairedMother (sectionAction b scale p direction)
          (sectionAction c scale p direction))) :=
  (source_gram p (sectionAction b scale p direction) (sectionAction c scale p direction)).symm

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
