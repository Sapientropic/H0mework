import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix BigOperators
noncomputable section

def complexMatrix (A : Matrix Basis Basis ℝ) : Matrix Basis Basis ℂ := A.map Complex.ofReal

theorem complexMatrix_mul (A B : Matrix Basis Basis ℝ) :
    complexMatrix (A*B) = complexMatrix A * complexMatrix B := by
  ext i j
  simp only [complexMatrix,Matrix.map_apply,Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]

theorem complexMatrix_one : complexMatrix 1 = 1 := by
  ext i j
  by_cases same : i=j <;> simp [complexMatrix,Matrix.one_apply,same]

def complexFrame : Matrix Basis Basis ℂ := complexMatrix normalizedSourceFrame
def complexDual : Matrix Basis Basis ℂ := complexMatrix sourceDualFrame

theorem complex_dual_frame (positive : actualGram.PosDef) : complexDual*complexFrame = 1 := by
  rw [complexDual,complexFrame,← complexMatrix_mul,dual_mul_frame positive,complexMatrix_one]

theorem complex_frame_dual (positive : actualGram.PosDef) : complexFrame*complexDual = 1 := by
  rw [complexDual,complexFrame,← complexMatrix_mul,frame_mul_dual positive,complexMatrix_one]

/-- Matrix actions are represented through the generated basis and its metric dual. -/
def normalizedAction (A : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ := complexDual*A*complexFrame

def originalAction (A : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ := complexFrame*A*complexDual

theorem action_recovered (positive : actualGram.PosDef) (A : Matrix Basis Basis ℂ) :
    originalAction (normalizedAction A) = A := by
  unfold originalAction normalizedAction
  calc
    _ = (complexFrame*complexDual)*A*(complexFrame*complexDual) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [complex_frame_dual positive]; simp

theorem action_composition (positive : actualGram.PosDef) (A B : Matrix Basis Basis ℂ) :
    normalizedAction A * normalizedAction B = normalizedAction (A*B) := by
  unfold normalizedAction
  calc
    _ = complexDual*A*(complexFrame*complexDual)*B*complexFrame := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [complex_frame_dual positive]; simp only [Matrix.mul_one,Matrix.mul_assoc]

theorem action_trace (positive : actualGram.PosDef) (A : Matrix Basis Basis ℂ) :
    (normalizedAction A).trace = A.trace := by
  unfold normalizedAction
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,complex_frame_dual positive,Matrix.one_mul]

theorem action_response (positive : actualGram.PosDef) (A D : Matrix Basis Basis ℂ) :
    (normalizedAction A * normalizedAction D).trace = (A*D).trace := by
  rw [action_composition positive,action_trace positive]

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
