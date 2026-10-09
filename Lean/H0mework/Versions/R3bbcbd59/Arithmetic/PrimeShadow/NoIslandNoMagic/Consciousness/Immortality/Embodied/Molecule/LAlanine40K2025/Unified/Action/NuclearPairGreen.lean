import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NuclearGreen
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenSource
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PrecisePair

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.PreciseNuclear
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open BasinRefinement SourceGaussianModel SourceCoulomb WholeBandBasin.Family.All.Nuclear GreenSource
noncomputable section

def pairEnergy (lengthUnit : ℝ) (first second : Fin 13) : ℝ :=
  (4*spinScale*nuclearCharge first)*(4*spinScale*nuclearCharge second)*
    green (sourcePosition lengthUnit first-sourcePosition lengthUnit second)

def repulsion (lengthUnit : ℝ) : ℝ :=
  ∑ pair ∈ (Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun pair => pair.1 < pair.2),
    pairEnergy lengthUnit pair.1 pair.2

theorem target_nuclei_distinct (first second : Fin 13) (different : first ≠ second) :
    PreciseTarget.centre first ≠ PreciseTarget.centre second := by
  have original : ∀ first second : Fin 13, first ≠ second →
      UnifiedOrbitals.Attraction.Precise.nucleus first ≠ UnifiedOrbitals.Attraction.Precise.nucleus second := by decide +kernel
  intro same
  apply original first second different
  funext index
  exact Rat.cast_injective (congrFun same index)

theorem source_nuclei_distinct (lengthUnit : ℝ) (positive : 0 < lengthUnit) (first second : Fin 13) (different : first ≠ second) :
    sourcePosition lengthUnit first ≠ sourcePosition lengthUnit second := by
  intro same
  apply target_nuclei_distinct first second different
  funext index
  exact mul_left_cancel₀ positive.ne' (congrFun same index)

theorem original_pair_green (lengthUnit : ℝ) (positive : 0 < lengthUnit) (first second : Fin 13) :
    pairEnergy lengthUnit first second = (4*spinScale)^2*greenCoefficient lengthUnit*PreciseTarget.nuclearRepulsion first second := by
  have displacement : sourcePosition lengthUnit first-sourcePosition lengthUnit second =
      lengthUnit • (PreciseTarget.centre first-PreciseTarget.centre second) := by simp [sourcePosition, smul_sub]
  rw [pairEnergy, displacement, green_scaled lengthUnit positive, PreciseTarget.nuclearRepulsion]
  ring

theorem original_repulsion_green (lengthUnit : ℝ) (positive : 0 < lengthUnit) :
    repulsion lengthUnit = (4*spinScale)^2*greenCoefficient lengthUnit*PreciseTarget.totalRepulsion := by
  simp only [repulsion, PreciseTarget.totalRepulsion, original_pair_green lengthUnit positive, Finset.mul_sum]

theorem pair_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun pair => pair.1 < pair.2)).card = 78 := by decide +kernel

theorem excludes_self (atom : Fin 13) :
    (atom,atom) ∉ (Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun pair => pair.1 < pair.2) := by simp

end
end LAlanine40K2025.UnifiedAction.PreciseNuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
