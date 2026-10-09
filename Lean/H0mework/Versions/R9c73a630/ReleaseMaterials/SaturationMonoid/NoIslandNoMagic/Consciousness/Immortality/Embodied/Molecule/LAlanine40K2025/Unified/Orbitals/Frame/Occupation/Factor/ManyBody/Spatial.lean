import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.OneBody

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix InnerProductSpace BigOperators
noncomputable section

abbrev SpinWaveSpace := Point × Bool → Hilbert

def coeffSlice (v : OneBody) (s : Bool) : Basis → ℂ := fun b => v (b,s)

def preparedSpinWave (time : ℝ) : OneBody →ₗ[ℂ] SpinWaveSpace where
  toFun := fun v z => sourceWave (coeffSlice v z.2) time z.1
  map_add' := by
    intro v w
    funext z
    simp [sourceWave,coeffSlice,Finset.sum_add_distrib,add_smul]
  map_smul' := by
    intro c v
    funext z
    simp [sourceWave,coeffSlice,Finset.smul_sum,smul_smul]

theorem prepared_wave_injective (time : ℝ) :
    Function.Injective (preparedSpinWave time) := by
  intro v w same
  have zero : preparedSpinWave time (v-w) = 0 := by
    rw [map_sub,same,sub_self]
  have each (b : Basis) (s : Bool) : v (b,s) = w (b,s) := by
    have waveZero (x : Point) : sourceWave (coeffSlice (v-w) s) time x = 0 := by
      exact congrFun zero (x,s)
    have pair := wave_pair_integral actual_gram_positive (Pi.single b (1 : ℂ))
      (coeffSlice (v-w) s) time
    have integralZero :
        (∫ x : Point, inner ℂ
          (sourceWave (Pi.single b (1 : ℂ)) time x)
          (sourceWave (coeffSlice (v-w) s) time x)) = 0 := by
      simp [waveZero]
    rw [integralZero] at pair
    have coefficient : (coeffSlice (v-w) s) b = 0 := by
      simpa [dotProduct,Pi.star_apply,Pi.single_apply] using pair.symm
    simpa [coeffSlice,Pi.sub_apply,sub_eq_zero] using coefficient
  funext z
  rcases z with ⟨b,s⟩
  exact each b s

def spatialSlaterState (time : ℝ) : ⋀[ℂ]^48 SpinWaveSpace :=
  exteriorPower.map 48 (preparedSpinWave time) slaterState

theorem spatial_slater_nonzero (time : ℝ) : spatialSlaterState time ≠ 0 := by
  intro zero
  have mapped : (exteriorPower.map 48 (preparedSpinWave time)) slaterState =
      (exteriorPower.map 48 (preparedSpinWave time)) 0 := by simpa [spatialSlaterState] using zero
  exact slater_nonzero ((exteriorPower.map_injective_field (n := 48)
    (prepared_wave_injective time)) mapped)

theorem spatial_slater_source (time : ℝ) :
    spatialSlaterState time =
      exteriorPower.ιMulti ℂ 48 (fun k => preparedSpinWave time (orbitalFamily k)) := by
  rw [spatialSlaterState]
  exact exteriorPower.map_apply_ιMulti _ _

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
