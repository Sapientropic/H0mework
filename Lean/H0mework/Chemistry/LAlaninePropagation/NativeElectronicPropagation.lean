import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Source matrices for finite electronic propagation

Only three quantized upper triangles enter this source. The lower triangles,
the fixed z-field Hamiltonian and the initial density matrix are reconstructed
from them; no evolution, target or correctness certificate is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Interface

abbrev Basis := Fin 98
abbrev UpperTriangle := Fin 4851 → Int

/-- All entries are real integers at scale `10^12`; density need not be a projector. -/
structure ElectronicPropagationSource where
  h0Q : UpperTriangle
  zQ : UpperTriangle
  d0Q : UpperTriangle

private theorem lastInRow_lt : ∀ row : Basis,
    row.val * (197 - row.val) / 2 + 97 - row.val < 4851 := by
  decide

/-- Row-major addressing of the source-owned upper triangle. -/
def upperIndex (i j : Basis) : Fin 4851 :=
  let lo := min i j
  let hi := max i j
  ⟨lo.val * (197 - lo.val) / 2 + hi.val - lo.val,
    lt_of_le_of_lt
      (Nat.sub_le_sub_right
        (Nat.add_le_add_left (Nat.le_of_lt_succ hi.isLt) _) _)
      (lastInRow_lt lo)⟩

theorem upperIndex_swap (i j : Basis) : upperIndex i j = upperIndex j i := by
  simp only [upperIndex, min_comm, max_comm]

def symmetricEntry (q : UpperTriangle) (i j : Basis) : Int :=
  q (upperIndex i j)

theorem symmetricEntry_swap (q : UpperTriangle) (i j : Basis) :
    symmetricEntry q i j = symmetricEntry q j i := by
  rw [symmetricEntry, symmetricEntry, upperIndex_swap]

def activeNumerator (source : ElectronicPropagationSource) (i j : Basis) : Int :=
  1000 * symmetricEntry source.h0Q i j + symmetricEntry source.zQ i j

noncomputable def activeMatrix (source : ElectronicPropagationSource) : Matrix Basis Basis ℂ :=
  fun i j => (activeNumerator source i j : ℂ) / 1000000000000000

noncomputable def initialDensityMatrix (source : ElectronicPropagationSource) :
    Matrix Basis Basis ℂ :=
  fun i j => (symmetricEntry source.d0Q i j : ℂ) / 1000000000000

end LAlanine40K2025.Propagation.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
