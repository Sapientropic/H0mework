import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Multiply
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem source_first_free_entries :
    ∀ i j : LoadPrimitive.NativeIndex,
      |((qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ) i j).1|+
      |((qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ) i j).2| ≤
      (3 : ℚ) := by
  decide +kernel

theorem source_donor_free_entries :
    ∀ i j : Fin 2 × Fin 2,
      |((qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ) i j).1|+
      |((qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ) i j).2| ≤
      (3 : ℚ) := by
  decide +kernel

theorem source_first_free_norm :
    ‖qvalue (qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ)‖ ≤
      (200 : ℝ) :=
  q_matrix_norm_le_200 _ (by decide) source_first_free_entries

theorem source_first_free_error :
    ‖value sourceFirstFreeInt-
      qvalue (qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ)‖ ≤
      (1/10^25 : ℝ) :=
  (quantize_error _ (by decide) (by decide)).trans (by norm_num)

theorem source_first_root_norm :
    ‖qvalue (rootOrdinaryQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (5000 : ℝ) := by
  let G := (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1
  change ‖qvalue ((rootGramQ G).submatrix tripleIndex tripleIndex)‖ ≤ _
  rw [qvalue_submatrix,Finite.reindex_norm]
  exact q_root_norm_le_5000 G (by decide) source_first_plus_factor_entries

theorem source_first_root_rotated_error :
    ‖value sourceFirstRootRotatedInt-
      qvalue (ordinaryRootRotatedQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^18 : ℝ) := by
  let UQ := qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ
  let RQ := rootOrdinaryQ (0 : Basis) (1 : Basis) (by decide)
  change ‖value (rotateInt sourceFirstFreeInt sourceFirstRootInt)-
    qvalue (rotateQ UQ RQ)‖ ≤ _
  rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
  exact rotate_int_bound sourceFirstFreeInt sourceFirstRootInt
    (qvalue UQ) (qvalue RQ) (by decide)
    source_first_free_error (by simpa only [sourceFirstRootInt] using
      source_first_ordinary_root_int_error)
    source_first_free_norm source_first_root_norm

theorem source_first_complement_norm :
    ‖qvalue (complementOrdinaryQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (5000 : ℝ) := by
  let G := (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2
  change ‖qvalue ((rootGramQ G).submatrix tripleIndex tripleIndex)‖ ≤ _
  rw [qvalue_submatrix,Finite.reindex_norm]
  exact q_root_norm_le_5000 G (by decide) source_first_minus_factor_entries

theorem source_first_complement_rotated_error :
    ‖value sourceFirstComplementRotatedInt-
      qvalue (ordinaryComplementRotatedQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^18 : ℝ) := by
  let UQ := qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ
  let RQ := complementOrdinaryQ (0 : Basis) (1 : Basis) (by decide)
  change ‖value (rotateInt sourceFirstFreeInt sourceFirstComplementInt)-
    qvalue (rotateQ UQ RQ)‖ ≤ _
  rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
  exact rotate_int_bound sourceFirstFreeInt sourceFirstComplementInt
    (qvalue UQ) (qvalue RQ) (by decide)
    source_first_free_error (by simpa only [sourceFirstComplementInt] using
      source_first_ordinary_complement_int_error)
    source_first_free_norm source_first_complement_norm

theorem source_donor_free_norm :
    ‖qvalue (qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ)‖ ≤
      (200 : ℝ) :=
  q_matrix_norm_le_200 _ (by decide) source_donor_free_entries

theorem source_donor_free_error :
    ‖value sourceDonorFreeInt-
      qvalue (qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ)‖ ≤
      (1/10^25 : ℝ) :=
  (quantize_error _ (by decide) (by decide)).trans (by norm_num)

theorem source_donor_root_norm : ‖qvalue rootDonorQ‖ ≤ (5000 : ℝ) := by
  let G := SquareRoot.Full.paidDonor.1
  change ‖qvalue ((rootGramQ G).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)‖ ≤ _
  rw [qvalue_submatrix,Finite.reindex_norm]
  exact q_root_norm_le_5000 G (by decide) source_donor_plus_factor_entries

theorem source_donor_complement_norm : ‖qvalue complementDonorQ‖ ≤ (5000 : ℝ) := by
  let G := SquareRoot.Full.paidDonor.2
  change ‖qvalue ((rootGramQ G).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex)‖ ≤ _
  rw [qvalue_submatrix,Finite.reindex_norm]
  exact q_root_norm_le_5000 G (by decide) source_donor_minus_factor_entries

theorem source_donor_root_rotated_error :
    ‖value sourceDonorRootRotatedInt-qvalue donorRootRotatedQ‖ ≤ (1/10^18 : ℝ) := by
  let UQ := qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ
  change ‖value (rotateInt sourceDonorFreeInt sourceDonorRootInt)-
    qvalue (rotateQ UQ rootDonorQ)‖ ≤ _
  rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
  exact rotate_int_bound sourceDonorFreeInt sourceDonorRootInt
    (qvalue UQ) (qvalue rootDonorQ) (by decide)
    source_donor_free_error (by simpa only [sourceDonorRootInt] using
      source_donor_root_int_error)
    source_donor_free_norm source_donor_root_norm

theorem source_donor_complement_rotated_error :
    ‖value sourceDonorComplementRotatedInt-qvalue donorComplementRotatedQ‖ ≤
      (1/10^18 : ℝ) := by
  let UQ := qkron (oneDiagonalQ (97 : Basis)) freeEnvironmentQ
  change ‖value (rotateInt sourceDonorFreeInt sourceDonorComplementInt)-
    qvalue (rotateQ UQ complementDonorQ)‖ ≤ _
  rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
  exact rotate_int_bound sourceDonorFreeInt sourceDonorComplementInt
    (qvalue UQ) (qvalue complementDonorQ) (by decide)
    source_donor_free_error (by simpa only [sourceDonorComplementInt] using
      source_donor_complement_int_error)
    source_donor_free_norm source_donor_complement_norm


end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
