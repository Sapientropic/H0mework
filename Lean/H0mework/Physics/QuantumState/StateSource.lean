import H0mework.Physics.QuantumState.SourceCoefficients
import H0mework.Physics.QuantumState.StateVector

/-! The accepted actual generates a normalized Gram state and a positive
evaluation on its complete occupied spin/color matrix algebra. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.State

open scoped ComplexOrder
open Matrix StageNineHolonomicField ProofFreeRicherAnholonomicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
  LAlanine40K2025.Thermal.Preparation

noncomputable section

abbrev Observable := Matrix Source.Index Source.Index ℂ

def preparation (point : BasePoint) : Observable :=
  column (Source.vector point) (0, 0)

def density (point : BasePoint) : Observable := normalizedGram (preparation point)

def evaluation (point : BasePoint) : Observable →ₗ[ℂ] ℂ :=
  vectorEvaluation (Source.vector point)

theorem density_posSemidef (point : BasePoint) : (density point).PosSemidef :=
  normalizedGram_posSemidef (preparation point)

theorem density_trace (point : BasePoint) : (density point).trace = 1 :=
  normalizedGram_trace _ (column_ne_zero _ _ (Source.vector_inner_self point))

theorem density_eq_pureMatrix (point : BasePoint) :
    density point = pureMatrix (Source.vector point) :=
  normalizedGram_column _ _ (Source.vector_inner_self point)

theorem evaluation_positive (point : BasePoint) (A : Observable) (hA : A.PosSemidef) :
    0 ≤ evaluation point A := vectorEvaluation_positive _ _ hA

theorem evaluation_one (point : BasePoint) : evaluation point 1 = 1 :=
  vectorEvaluation_one _ (Source.vector_inner_self point)

theorem evaluation_eq_trace (point : BasePoint) (A : Observable) :
    evaluation point A = (density point * A).trace := by
  rw [density_eq_pureMatrix]
  exact vectorEvaluation_eq_trace _ _

structure Effect where
  matrix : Observable
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

def Effect.complement (effect : Effect) : Effect where
  matrix := 1 - effect.matrix
  positive := effect.complement_positive
  complement_positive := by simpa using effect.positive

def effectWeight (point : BasePoint) (effect : Effect) : ℝ :=
  (evaluation point effect.matrix).re

theorem effectWeight_nonnegative (point : BasePoint) (effect : Effect) :
    0 ≤ effectWeight point effect :=
  (Complex.nonneg_iff.mp (evaluation_positive point _ effect.positive)).1

theorem effectWeight_complement (point : BasePoint) (effect : Effect) :
    effectWeight point effect.complement = 1 - effectWeight point effect := by
  change (evaluation point (1 - effect.matrix)).re = _
  rw [map_sub, evaluation_one]
  rfl

theorem effectWeight_le_one (point : BasePoint) (effect : Effect) :
    effectWeight point effect ≤ 1 := by
  have nonnegative := effectWeight_nonnegative point effect.complement
  rw [effectWeight_complement] at nonnegative
  linarith

theorem effectWeight_binary_normalized (point : BasePoint) (effect : Effect) :
    effectWeight point effect + effectWeight point effect.complement = 1 := by
  rw [effectWeight_complement]
  ring

def sourceEffect (reference : BasePoint) : Effect where
  matrix := pureMatrix (Source.vector reference)
  positive := pureMatrix_posSemidef _
  complement_positive := pureMatrix_complement_posSemidef _ (Source.vector_inner_self reference)

theorem effectWeight_sourceEffect (point reference : BasePoint) :
    effectWeight point (sourceEffect reference) =
      Complex.normSq (star (Source.vector reference) ⬝ᵥ Source.vector point) := by
  change (vectorEvaluation _ (pureMatrix _)).re = _
  rw [vectorEvaluation_pureMatrix, Complex.ofReal_re]

theorem effectWeight_sourceEffect_self (point : BasePoint) :
    effectWeight point (sourceEffect point) = 1 := by
  rw [effectWeight_sourceEffect]
  have normalized : star (Source.vector point) ⬝ᵥ Source.vector point = 1 :=
    Source.vector_inner_self point
  rw [normalized, Complex.normSq_one]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.State
