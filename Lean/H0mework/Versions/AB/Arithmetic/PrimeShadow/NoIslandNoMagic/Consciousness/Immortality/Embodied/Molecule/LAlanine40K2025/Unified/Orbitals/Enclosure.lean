import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coefficients
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.SquareRoot
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Exponential

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceSignedEvaluator

structure SqrtMaterial where
  gamma : ℚ
  interval : Pair
  deriving Inhabited

structure SqrtComputed (m : SqrtMaterial) : Prop where
  positive : 0 < m.gamma
  nonnegative : 0 ≤ m.interval.2
  lower : m.interval.1^2*m.gamma ≤ piLower
  upper : piUpper ≤ m.interval.2^2*m.gamma

theorem sqrt_material_contains (m : SqrtMaterial) (h : SqrtComputed m) :
    Holds m.interval (Real.sqrt (Real.pi/m.gamma)) :=
  sqrt_pi_contains m.gamma m.interval.1 m.interval.2 h.positive h.nonnegative h.lower h.upper

structure ExpMaterial where
  penalty : ℚ
  steps : ℕ
  interval : Pair
  deriving Inhabited

structure ExpComputed (m : ExpMaterial) : Prop where
  valid : ExpReductionValid m.penalty m.steps
  value : m.interval = negativeExp m.penalty m.steps

theorem exp_material_contains (m : ExpMaterial) (h : ExpComputed m) :
    Holds m.interval (Real.exp (-(m.penalty : ℝ))) := by
  rw [h.value]
  exact negative_exp_contains m.penalty m.steps h.valid

structure RadialMaterial where
  gamma : ℚ
  penalty : ℚ
  interval : Pair
  deriving Inhabited

def combineRadial (s : SqrtMaterial) (e : ExpMaterial) : RadialMaterial :=
  ⟨s.gamma,e.penalty,mul e.interval (mul s.interval (square s.interval))⟩

theorem combined_radial_contains (s : SqrtMaterial) (e : ExpMaterial)
    (hs : SqrtComputed s) (he : ExpComputed e) :
    Holds (combineRadial s e).interval (radialKernel s.gamma e.penalty) := by
  have root := sqrt_material_contains s hs
  have result := mul_holds _ _ _ _ (exp_material_contains e he)
    (mul_holds _ _ _ _ root (square_holds _ _ root))
  simpa only [combineRadial,radialKernel,pow_succ,pow_two,mul_assoc,mul_comm,mul_left_comm] using result

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
