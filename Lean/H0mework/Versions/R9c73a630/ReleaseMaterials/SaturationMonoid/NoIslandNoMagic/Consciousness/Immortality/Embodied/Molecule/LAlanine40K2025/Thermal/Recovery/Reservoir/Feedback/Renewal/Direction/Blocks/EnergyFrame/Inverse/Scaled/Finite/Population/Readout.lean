import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.TopPopulation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.PureDonor

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Population
open Collision Load.Source Load.Producer.StrictThermal Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Weak.execution sourceTarget sourceInitial SquareRoot.Full.sourcePointer
  afterInstrumentEleven SquareRoot.finitePointer

private theorem energy_pulled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    energy O (Quantum.conjugation U rho) = energy (Quantum.conjugation (star U) O) rho :=
  energy_pullback O rho U

theorem original_source_eleven_readout_error (O : PointerJoint) :
    |energy O Weak.execution.joint - energy O SquareRoot.Full.sourceEleven| ≤
      (57/10^6 : ℝ) * ‖O‖ := by
  let pulled : PointerJoint := Quantum.conjugation (star afterInstrumentEleven) O
  have pulled_norm : ‖pulled‖ = ‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint (star afterInstrumentEleven)) O
  have original_read : energy O Weak.execution.joint = energy pulled sourceTarget := by
    rw [original_eleven_from_instrument]
    exact energy_pullback O sourceTarget afterInstrumentEleven
  have reference_read : energy O SquareRoot.Full.sourceEleven =
      energy pulled (SquareRoot.rawConjugation SquareRoot.Full.sourcePointer sourceInitial) := by
    rw [SquareRoot.Full.sourceEleven, SquareRoot.approximatedEleven, energy_pulled,
      SquareRoot.approximatedTarget, SquareRoot.Full.sourcePointer]
  have first := SquareRoot.original_finite_pointer_observable pulled
  have second := SquareRoot.raw_observable_error pulled sourceInitial
    sourceInitial_positive sourceInitial_trace SquareRoot.finitePointer SquareRoot.Full.sourcePointer
  have pointer_norm : ‖SquareRoot.Full.sourcePointer‖ ≤ 1 + (4/10^7 : ℝ) := by
    rw [SquareRoot.Full.sourcePointer]
    exact SquareRoot.approximated_pointer_norm _ _ SquareRoot.Full.source_whole_roots_error.1
      SquareRoot.Full.source_whole_roots_error.2
  have second_bound : |energy pulled (Quantum.conjugation SquareRoot.finitePointer sourceInitial) -
      energy pulled (SquareRoot.rawConjugation SquareRoot.Full.sourcePointer sourceInitial)| ≤
        (81/10^8 : ℝ) * ‖pulled‖ := by
    apply second.trans
    calc
      _ ≤ (1+(1+(4/10^7 : ℝ))) * ‖pulled‖ * (4/10^7) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) pointer_norm) (norm_nonneg pulled))
          SquareRoot.Full.source_pointer_error (norm_nonneg _)
          (mul_nonneg (by norm_num) (norm_nonneg pulled))
      _ ≤ (81/10^8 : ℝ) * ‖pulled‖ := by nlinarith [norm_nonneg pulled]
  rw [original_read, reference_read]
  have triangle := abs_sub_le (energy pulled sourceTarget)
    (energy pulled (Quantum.conjugation SquareRoot.finitePointer sourceInitial))
    (energy pulled (SquareRoot.rawConjugation SquareRoot.Full.sourcePointer sourceInitial))
  rw [pulled_norm] at first second_bound
  linarith [norm_nonneg O]

def pcObservable (H : Matrix PairController PairController ℂ) : PointerJoint :=
  pointerDiagonal (Post.pcLift H)

private theorem tensor_left_energy {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι ι ℂ)
    (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (Matrix.kronecker (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (1 : Matrix κ κ ℂ)) rho =
      energy H (Collision.systemReduce (Powered.Dynamics.systemReduce rho)) := by
  have outer := Powered.Dynamics.jointEnergy_real_eq_reduced
    (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (0 : Matrix κ κ ℂ) rho
  have first : energy (Matrix.kronecker (Matrix.kronecker H (1 : Matrix ι ι ℂ))
      (1 : Matrix κ κ ℂ)) rho =
      energy (Matrix.kronecker H (1 : Matrix ι ι ℂ))
        (Powered.Dynamics.systemReduce rho) := by
    simpa [energy, Matrix.kronecker] using outer
  rw [first, Exchange.left_energy]

theorem pc_lift_energy (H : Matrix PairController PairController ℂ) (rho : Current.FullJoint) :
    energy (Post.pcLift H) rho = energy H (Resource.pcMatrixOf rho) := tensor_left_energy H rho

theorem pc_observable_energy (H : Matrix PairController PairController ℂ) (rho : PointerJoint) :
    energy (pcObservable H) rho = energy H (Resource.pcMatrixOf (bodyRead rho)) := by
  have split := block_energy_split (Post.pcLift H) 0 rho
  simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_mul] at split
  exact split.trans (pc_lift_energy H (bodyRead rho))

theorem pc_observable_norm (H : Matrix PairController PairController ℂ) :
    ‖pcObservable H‖ ≤ ‖H‖ :=
  (Post.diagonal_norm_le _).trans (Post.pc_lift_norm H)

theorem original_source_pc_readout_error (H : Matrix PairController PairController ℂ) :
    |energy H (Resource.pcMatrixOf (bodyRead Weak.execution.joint)) -
      energy H (Resource.pcMatrixOf (bodyRead SquareRoot.Full.sourceEleven))| ≤
      (57/10^6 : ℝ) * ‖H‖ := by
  have paid := original_source_eleven_readout_error (pcObservable H)
  rw [pc_observable_energy, pc_observable_energy] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (pc_observable_norm H) (by norm_num))

def rootReadout (O : PointerJoint) : PointerJoint :=
  star SquareRoot.Full.sourcePointer * Quantum.conjugation (star afterInstrumentEleven) O *
    SquareRoot.Full.sourcePointer

def suppliedReadout (O : PointerJoint) : Current.FullJoint :=
  Quantum.conjugation (star (Current.pulse (nativeClockStep : ℝ))) (Prepared.pointerReadout (rootReadout O))

def finiteLoadedReadout (O : PointerJoint) : LoadedJoint :=
  Supply.finiteDonorReadout (suppliedReadout O)

def finiteInputRead (O : PointerJoint) : ℝ :=
  energy (Quantum.conjugation installedLoadFrame (finiteLoadedReadout O)) Actions.finiteReceivedBody

attribute [local irreducible] Current.pulse

theorem root_readout_hermitian (O : PointerJoint) (hO : O.IsHermitian) :
    (rootReadout O).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose (star SquareRoot.Full.sourcePointer)
    (Prepared.conjugation_hermitian (star afterInstrumentEleven) O hO)
  simpa only [rootReadout, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

theorem root_readout_norm (O : PointerJoint) : ‖rootReadout O‖ ≤ 2*‖O‖ := by
  have h := Prepared.sandwich_norm SquareRoot.Full.sourcePointer
    (Quantum.conjugation (star afterInstrumentEleven) O)
  have n : ‖Quantum.conjugation (star afterInstrumentEleven) O‖ = ‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint (star afterInstrumentEleven)) O
  rw [n] at h
  have sourceNorm : ‖SquareRoot.Full.sourcePointer‖ ≤ 1+(4/10^7 : ℝ) := by
    rw [SquareRoot.Full.sourcePointer]
    exact SquareRoot.approximated_pointer_norm _ _ SquareRoot.Full.source_whole_roots_error.1
      SquareRoot.Full.source_whole_roots_error.2
  have sq := pow_le_pow_left₀ (norm_nonneg SquareRoot.Full.sourcePointer) sourceNorm 2
  exact h.trans (mul_le_mul_of_nonneg_right (sq.trans (by norm_num)) (norm_nonneg O))

theorem supplied_readout_hermitian (O : PointerJoint) (hO : O.IsHermitian) :
    (suppliedReadout O).IsHermitian :=
  Prepared.conjugation_hermitian _ _ (Prepared.pointer_readout_hermitian _ (root_readout_hermitian O hO))

theorem supplied_readout_norm (O : PointerJoint) (hO : O.IsHermitian) :
    ‖suppliedReadout O‖ ≤ 2*‖O‖ := by
  have same : ‖suppliedReadout O‖ = ‖Prepared.pointerReadout (rootReadout O)‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ Current.FullJoint
      (star (Current.pulse (nativeClockStep : ℝ)))) (Prepared.pointerReadout (rootReadout O))
  rw [same]
  exact (Prepared.pointer_readout_norm _ (root_readout_hermitian O hO)).trans (root_readout_norm O)

theorem finite_loaded_readout_hermitian (O : PointerJoint) (hO : O.IsHermitian) :
    (finiteLoadedReadout O).IsHermitian :=
  Supply.finite_donor_readout_hermitian _ (supplied_readout_hermitian O hO)

theorem finite_loaded_readout_norm (O : PointerJoint) (hO : O.IsHermitian) :
    ‖finiteLoadedReadout O‖ ≤ 2*‖O‖ :=
  (Supply.finite_donor_readout_norm _ (supplied_readout_hermitian O hO)).trans
    (supplied_readout_norm O hO)

theorem source_root_read (O : PointerJoint) :
    energy O SquareRoot.Full.sourceEleven = energy (rootReadout O) sourceInitial := by
  rw [SquareRoot.Full.sourceEleven, SquareRoot.approximatedEleven, energy_pulled,
    SquareRoot.approximatedTarget, SquareRoot.raw_pullback]
  rw [rootReadout, SquareRoot.Full.sourcePointer]

theorem source_donor_read (O : PointerJoint) :
    energy O SquareRoot.Full.sourceEleven = energy (Prepared.donorReadout (suppliedReadout O)) Source.received.joint := by
  rw [source_root_read, sourceInitial, Prepared.pointer_readout_energy, Prepared.supply_readout_energy]
  rfl

theorem original_finite_input_read_error (O : PointerJoint) (hO : O.IsHermitian) :
    |energy O Weak.execution.joint - finiteInputRead O| ≤ (7/10^5 : ℝ)*‖O‖ := by
  have root := original_source_eleven_readout_error O
  have donor := Supply.original_finite_donor_energy_error_sharp (suppliedReadout O)
  rw [← source_donor_read] at donor
  have input := Actions.original_finite_received_energy_error (finiteLoadedReadout O)
    (finite_loaded_readout_hermitian O hO)
  have donorBound : |energy O SquareRoot.Full.sourceEleven - energy (finiteLoadedReadout O) Source.received.joint| ≤
      (4/10^9 : ℝ)*‖O‖ :=
    donor.trans (by nlinarith [supplied_readout_norm O hO])
  have inputBound : |energy (finiteLoadedReadout O) Source.received.joint - finiteInputRead O| ≤
      (106/10^7 : ℝ)*‖O‖ :=
    input.trans (by nlinarith [finite_loaded_readout_norm O hO])
  have t1 := abs_sub_le (energy O Weak.execution.joint) (energy O SquareRoot.Full.sourceEleven)
    (energy (finiteLoadedReadout O) Source.received.joint)
  have t2 := abs_sub_le (energy O Weak.execution.joint)
    (energy (finiteLoadedReadout O) Source.received.joint) (finiteInputRead O)
  linarith [norm_nonneg O]

open Evaluation

def calculatedWord : PointerJoint :=
  (Post.calculatedEleven : PointerJoint) * Post.calculatedSourcePointer *
    pointerDiagonal (Supply.calculatedSupply : Current.FullJoint)

def referenceWord : PointerJoint :=
  LoadExecution.eleven * PCExecution.pointer * pointerDiagonal PCExecution.supply

attribute [local irreducible] Post.calculatedEleven Post.calculatedSourcePointer Supply.calculatedSupply
  LoadExecution.eleven PCExecution.pointer PCExecution.supply Post.elevenPolynomial PCExecution.eleven
  Post.finiteSourcePointer Supply.fullSupplyPolynomial

theorem source_eleven_word_error :
    ‖(Post.calculatedEleven : PointerJoint) - LoadExecution.eleven‖ ≤ (1/10^12 : ℝ) := by
  have t1 := norm_sub_le_norm_sub_add_norm_sub (Post.calculatedEleven : PointerJoint)
    Post.elevenPolynomial PCExecution.eleven
  have t2 := norm_sub_le_norm_sub_add_norm_sub (Post.calculatedEleven : PointerJoint)
    PCExecution.eleven LoadExecution.eleven
  linarith only [t1,t2,Post.original_eleven_polynomial_error,PCExecution.eleven_error,LoadExecution.eleven_error]

theorem source_pointer_word_error :
    ‖Post.calculatedSourcePointer - PCExecution.pointer‖ ≤ (1/10^16 : ℝ) := by
  have t := norm_sub_le_norm_sub_add_norm_sub Post.calculatedSourcePointer Post.finiteSourcePointer PCExecution.pointer
  linarith only [t,Post.original_finite_source_pointer_error,PCExecution.pointer_error]

theorem source_supply_word_error :
    ‖(Supply.calculatedSupply : Current.FullJoint) - PCExecution.supply‖ ≤ (1/10^12 : ℝ) := by
  have t := norm_sub_le_norm_sub_add_norm_sub (Supply.calculatedSupply : Current.FullJoint)
    Supply.fullSupplyPolynomial PCExecution.supply
  linarith only [t,Supply.original_supply_polynomial_error,PCExecution.supply_error]

private theorem product_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (a b : ℝ) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b) : ‖A*B‖ ≤ a*b :=
  (norm_mul_le A B).trans (mul_le_mul ha hb (norm_nonneg B) ((norm_nonneg A).trans ha))

theorem calculated_word_norm : ‖calculatedWord‖ ≤ 2 := by
  have prefixNorm : ‖(Post.calculatedEleven : PointerJoint) * Post.calculatedSourcePointer‖ ≤ 2 := by
    have h := product_norm_bound (Post.calculatedEleven : PointerJoint) Post.calculatedSourcePointer 1 2
      (le_of_eq (CStarRing.norm_coe_unitary _)) (Post.calculated_source_pointer_norm.trans (by norm_num))
    simpa only [one_mul] using h
  have supplyNorm : ‖pointerDiagonal (Supply.calculatedSupply : Current.FullJoint)‖ ≤ 1 :=
    (Post.diagonal_norm_le _).trans (le_of_eq (CStarRing.norm_coe_unitary _))
  exact (product_norm_bound _ _ 2 1 prefixNorm supplyNorm).trans (by norm_num)

theorem reference_word_norm : ‖referenceWord‖ ≤ 36 := by
  have prefixNorm : ‖LoadExecution.eleven * PCExecution.pointer‖ ≤ 12 :=
    (product_norm_bound _ _ 4 3 LoadExecution.eleven_norm PCExecution.pointer_norm).trans (by norm_num)
  have supplyNorm : ‖pointerDiagonal PCExecution.supply‖ ≤ 3 :=
    (Post.diagonal_norm_le _).trans PCExecution.supply_norm
  exact (product_norm_bound _ _ 12 3 prefixNorm supplyNorm).trans (by norm_num)

theorem source_reference_word_error : ‖calculatedWord-referenceWord‖ ≤ (1/10^9 : ℝ) := by
  have prefixError : ‖(Post.calculatedEleven : PointerJoint)*Post.calculatedSourcePointer -
      LoadExecution.eleven*PCExecution.pointer‖ ≤ (1/10^11 : ℝ) := by
    have h := PCExecution.product_change (Post.calculatedEleven : PointerJoint) Post.calculatedSourcePointer
      LoadExecution.eleven PCExecution.pointer
    apply h.trans
    have p := mul_le_mul source_eleven_word_error
      (Post.calculated_source_pointer_norm.trans (show (1+(4/10^7 : ℝ)) ≤ 2 by norm_num))
      (norm_nonneg _) (by norm_num)
    have q := mul_le_mul LoadExecution.eleven_norm source_pointer_word_error
      (norm_nonneg _) (by norm_num)
    exact (add_le_add p q).trans (by norm_num)
  have diagError : ‖pointerDiagonal (Supply.calculatedSupply : Current.FullJoint) -
      pointerDiagonal PCExecution.supply‖ ≤ (1/10^12 : ℝ) := by
    rw [← map_sub]
    exact (Post.diagonal_norm_le _).trans source_supply_word_error
  have sourceNorm : ‖pointerDiagonal (Supply.calculatedSupply : Current.FullJoint)‖ ≤ 1 :=
    (Post.diagonal_norm_le _).trans (le_of_eq (CStarRing.norm_coe_unitary _))
  have prefixNorm : ‖LoadExecution.eleven*PCExecution.pointer‖ ≤ 12 :=
    (product_norm_bound _ _ 4 3 LoadExecution.eleven_norm PCExecution.pointer_norm).trans (by norm_num)
  have h := PCExecution.product_change ((Post.calculatedEleven : PointerJoint)*Post.calculatedSourcePointer)
    (pointerDiagonal (Supply.calculatedSupply : Current.FullJoint)) (LoadExecution.eleven*PCExecution.pointer)
    (pointerDiagonal PCExecution.supply)
  apply h.trans
  exact (add_le_add (mul_le_mul prefixError sourceNorm (norm_nonneg _) (by norm_num))
    (mul_le_mul prefixNorm diagError (norm_nonneg _) (by norm_num))).trans (by norm_num)

def wordReadout (W O : PointerJoint) : LoadedJoint :=
  Supply.donorSlice (Prepared.pointerReadout (star W*O*W))

private theorem corner_raw_pullback {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℂ) (O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    Prepared.pointerReadout (star (pointerDiagonal S)*O*pointerDiagonal S) =
      star S*Prepared.pointerReadout O*S := by
  rw [← map_star]
  change (Matrix.fromBlocks (star S) 0 0 (star S)*O*Matrix.fromBlocks S 0 0 S).toBlocks₁₁ = _
  conv_lhs => arg 1; arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks O]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rfl

private theorem word_corner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E P O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (S : Matrix ι ι ℂ) :
    Prepared.pointerReadout (star (E*P*pointerDiagonal S)*O*(E*P*pointerDiagonal S)) =
      star S*Prepared.pointerReadout (star P*(star E*O*E)*P)*S := by
  have rearrange : star (E*P*pointerDiagonal S)*O*(E*P*pointerDiagonal S) =
      star (pointerDiagonal S)*(star P*(star E*O*E)*P)*pointerDiagonal S := by
    simp only [star_mul, mul_assoc]
  rw [rearrange, corner_raw_pullback]

theorem root_coordinates (O : PointerJoint) :
    Quantum.conjugation Supply.installedFullFrame (Prepared.pointerReadout (rootReadout O)) =
      Prepared.pointerReadout (star Post.calculatedSourcePointer *
        Quantum.conjugation (star Post.calculatedEleven) (Quantum.conjugation Post.pointerFrame O) *
          Post.calculatedSourcePointer) := by
  rw [Post.corner_conjugation]
  change Prepared.pointerReadout (Quantum.conjugation Post.pointerFrame (rootReadout O)) = _
  rw [rootReadout, Post.raw_pullback_covariance, Post.conjugated_pullback,
    Post.calculatedSourcePointer, Post.calculatedEleven]

theorem finite_input_word (O : PointerJoint) : finiteInputRead O =
    energy (wordReadout calculatedWord (Quantum.conjugation Post.pointerFrame O)) Actions.finiteReceivedBody := by
  rw [finiteInputRead, finiteLoadedReadout, Supply.finite_donor_read_as_slice,
    suppliedReadout, Post.conjugated_pullback, root_coordinates]
  rw [wordReadout, calculatedWord, word_corner]
  simp only [Supply.calculatedSupply, Quantum.conjugation_apply, Unitary.coe_star, star_star]

theorem word_readout_hermitian (W O : PointerJoint) (hO : O.IsHermitian) :
    (wordReadout W O).IsHermitian :=
  Post.donor_slice_hermitian _ (Prepared.pointer_readout_hermitian _ (Supply.raw_pullback_hermitian W O hO))

theorem word_readout_norm (W O : PointerJoint) (hO : O.IsHermitian) :
    ‖wordReadout W O‖ ≤ ‖W‖^2*‖O‖ :=
  (Post.donor_slice_norm _ (Prepared.pointer_readout_hermitian _ (Supply.raw_pullback_hermitian W O hO))).trans
    ((Prepared.pointer_readout_norm _ (Supply.raw_pullback_hermitian W O hO)).trans (Prepared.sandwich_norm W O))

private theorem corner_sub {ι : Type*} (A B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    Prepared.pointerReadout A-Prepared.pointerReadout B = Prepared.pointerReadout (A-B) := rfl

theorem word_readout_difference (A B O : PointerJoint) (hO : O.IsHermitian) :
    ‖wordReadout A O-wordReadout B O‖ ≤ (‖A‖+‖B‖)*‖O‖*‖A-B‖ := by
  have herm := (Supply.raw_pullback_hermitian A O hO).sub (Supply.raw_pullback_hermitian B O hO)
  change ‖Supply.donorSlice (Prepared.pointerReadout (star A*O*A)) -
    Supply.donorSlice (Prepared.pointerReadout (star B*O*B))‖ ≤ _
  rw [← Post.donor_slice_sub]
  rw [corner_sub]
  exact (Post.donor_slice_norm _ (Prepared.pointer_readout_hermitian _ herm)).trans
    ((Prepared.pointer_readout_norm _ herm).trans (Post.raw_sandwich_change A B O))

theorem calculated_reference_readout_error (O : PointerJoint) (hO : O.IsHermitian) :
    ‖wordReadout calculatedWord O-wordReadout referenceWord O‖ ≤ (1/10^7 : ℝ)*‖O‖ := by
  have h := word_readout_difference calculatedWord referenceWord O hO
  have scaled := mul_le_mul
    (mul_le_mul_of_nonneg_right (add_le_add calculated_word_norm reference_word_norm) (norm_nonneg O))
    source_reference_word_error (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg O))
  exact h.trans (scaled.trans (by nlinarith [norm_nonneg O]))

private theorem energy_difference {ι : Type*} [Fintype ι] (A B rho : Matrix ι ι ℂ) :
    energy A rho-energy B rho=energy (A-B) rho := by
  simp only [energy, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

def referenceInputRead (O : PointerJoint) : ℝ :=
  energy (wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O)) Actions.finiteReceivedBody

theorem finite_reference_input_error (O : PointerJoint) (hO : O.IsHermitian) :
    |finiteInputRead O-referenceInputRead O| ≤ (2/10^7 : ℝ)*‖O‖ := by
  rw [finite_input_word, referenceInputRead, energy_difference]
  have hFrame := Prepared.conjugation_hermitian Post.pointerFrame O hO
  have h := Post.finite_body_energy_norm
    (wordReadout calculatedWord (Quantum.conjugation Post.pointerFrame O) -
      wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O))
    ((word_readout_hermitian _ _ hFrame).sub (word_readout_hermitian _ _ hFrame))
  have err := calculated_reference_readout_error (Quantum.conjugation Post.pointerFrame O) hFrame
  have normFrame : ‖Quantum.conjugation Post.pointerFrame O‖ = ‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint Post.pointerFrame) O
  rw [normFrame] at err
  exact h.trans ((mul_le_mul_of_nonneg_left err (by norm_num)).trans (by nlinarith [norm_nonneg O]))

theorem original_reference_input_error (O : PointerJoint) (hO : O.IsHermitian) :
    |energy O Weak.execution.joint-referenceInputRead O| ≤ (1/10^4 : ℝ)*‖O‖ := by
  have triangle := abs_sub_le (energy O Weak.execution.joint) (finiteInputRead O) (referenceInputRead O)
  linarith [original_finite_input_read_error O hO, finite_reference_input_error O hO, norm_nonneg O]

open NetContraction.Fixed

def positiveReceivedBody : LoadedJoint :=
  LoadExecution.receivedWord*positiveReferenceInput*star LoadExecution.receivedWord

theorem positive_received_body : positiveReceivedBody.PosSemidef := by
  simpa only [positiveReceivedBody, Matrix.star_eq_conjTranspose] using
    positive_reference_input.mul_mul_conjTranspose_same LoadExecution.receivedWord

attribute [local irreducible] LoadExecution.receivedWord InputProducts.bodyInput positiveReferenceInput

theorem finite_positive_received_error :
    ‖Actions.finiteReceivedBody-positiveReceivedBody‖ ≤ (1/10^12 : ℝ) := by
  have finalError : ‖InputProducts.body-positiveReceivedBody‖ ≤ (1/10^15 : ℝ) := by
    have h := Input.raw_input_error LoadExecution.receivedWord InputProducts.bodyInput positiveReferenceInput
    have word := source_received_word_norm_sharp
    have square := pow_le_pow_left₀ (norm_nonneg LoadExecution.receivedWord) word 2
    exact h.trans ((mul_le_mul square source_reference_input_error (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have t1 := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody Diagonal.computedBody Field.computedBody
  have t2 := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody Field.computedBody PCExecution.receivedBody
  have t3 := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody PCExecution.receivedBody LoadExecution.receivedBody
  have t4 := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody LoadExecution.receivedBody InputProducts.body
  have t5 := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody InputProducts.body positiveReceivedBody
  linarith only [t1,t2,t3,t4,t5,Diagonal.computed_body_error,Field.body_numeric_error,
    PCExecution.body_error,LoadExecution.body_error,InputProducts.body_error,finalError]

def positiveReferenceRead (O : PointerJoint) : ℝ :=
  energy (wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O)) positiveReceivedBody

theorem reference_positive_input_error (O : PointerJoint) (hO : O.IsHermitian) :
    |referenceInputRead O-positiveReferenceRead O| ≤ (1/10^4 : ℝ)*‖O‖ := by
  have hFrame := Prepared.conjugation_hermitian Post.pointerFrame O hO
  have normFrame : ‖Quantum.conjugation Post.pointerFrame O‖ = ‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint Post.pointerFrame) O
  have readNorm : ‖wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O)‖ ≤ 1296*‖O‖ := by
    have h := word_readout_norm referenceWord (Quantum.conjugation Post.pointerFrame O) hFrame
    rw [normFrame] at h
    have sq := pow_le_pow_left₀ (norm_nonneg referenceWord) reference_word_norm 2
    exact h.trans (mul_le_mul_of_nonneg_right (sq.trans (by norm_num)) (norm_nonneg O))
  have delta : referenceInputRead O-positiveReferenceRead O =
      energy (wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O))
        (Actions.finiteReceivedBody-positiveReceivedBody) := by
    simp only [referenceInputRead,positiveReferenceRead,energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  rw [delta]
  have h := Input.energy_dimension_norm (wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O))
    (Actions.finiteReceivedBody-positiveReceivedBody)
  have dimension : (Fintype.card (PairController × Fin 2) : ℝ) = 38416 := by
    norm_num [PairController,Propagation.Interface.Basis]
  rw [dimension] at h
  have bounded : (38416 : ℝ)*‖wordReadout referenceWord (Quantum.conjugation Post.pointerFrame O)‖*
      ‖Actions.finiteReceivedBody-positiveReceivedBody‖ ≤ 38416*(1296*‖O‖)*(1/10^12) := mul_le_mul
    (mul_le_mul_of_nonneg_left readNorm (by norm_num)) finite_positive_received_error
    (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg O)))
  exact h.trans (bounded.trans (by nlinarith [norm_nonneg O]))

theorem original_positive_reference_error (O : PointerJoint) (hO : O.IsHermitian) :
    |energy O Weak.execution.joint-positiveReferenceRead O| ≤ (1/1000 : ℝ)*‖O‖ := by
  have t := abs_sub_le (energy O Weak.execution.joint) (referenceInputRead O) (positiveReferenceRead O)
  linarith [original_reference_input_error O hO, reference_positive_input_error O hO, norm_nonneg O]

def rho11 : Matrix PairController PairController ℂ := Resource.pcMatrixOf (bodyRead Weak.execution.joint)

theorem rho11_positive : rho11.PosSemidef :=
  Collision.systemReduce_posSemidef _ (Powered.Dynamics.systemReduce_posSemidef _
    ((Weak.execution.positive.submatrix Sum.inl).add (Weak.execution.positive.submatrix Sum.inr)))

private theorem body_trace {ι : Type*} [Fintype ι] (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (bodyRead rho).trace=rho.trace := by
  rw [bodyRead, Matrix.trace_add]
  have h := trace_fromBlocks rho.toBlocks₁₁ rho.toBlocks₁₂ rho.toBlocks₂₁ rho.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at h
  exact h.symm

theorem rho11_trace : rho11.trace=1 := by
  rw [rho11,Resource.pcMatrixOf,Collision.systemReduce_trace,Powered.Dynamics.systemReduce_trace,
    body_trace,Weak.execution.normalized]

theorem pc_observable_hermitian (H : Matrix PairController PairController ℂ) (hH : H.IsHermitian) :
    (pcObservable H).IsHermitian :=
  Prepared.doubled_hermitian _ (Prepared.tensor_hermitian _ _
    (Prepared.tensor_hermitian _ _ hH (by simp)) (by simp))

theorem pc_observable_covariance (H : Matrix PairController PairController ℂ) :
    Quantum.conjugation Post.pointerFrame (pcObservable H) =
      pcObservable (Quantum.conjugation installedPCFrame H) := by
  change Quantum.conjugation (blockUnitary Supply.installedFullFrame Supply.installedFullFrame)
    (pointerDiagonal (Post.pcLift H)) = _
  rw [Post.diagonal_conjugation]
  exact congrArg pointerDiagonal (Post.pc_lift_covariance installedPCFrame H)

def positiveHighRead : ℝ :=
  energy (wordReadout referenceWord (pcObservable Donor.calculatedDonor)) positiveReceivedBody

theorem finite_high_reference :
    positiveReferenceRead (pcObservable Supply.sourceFiniteDonor) = positiveHighRead := by
  rw [positiveReferenceRead,pc_observable_covariance,Supply.finite_donor_calculated]
  rfl

theorem original_top_reference_error :
    |energy Source.donor rho11-positiveHighRead| ≤ (2/1000 : ℝ) := by
  have finiteNorm : ‖Supply.sourceFiniteDonor‖ ≤ 1 := by
    have h := positive_norm_le_trace_re Supply.sourceFiniteDonor Supply.finite_donor_positive
    rw [Supply.finite_donor_trace,Complex.one_re] at h
    exact h
  have observableNorm : ‖pcObservable Supply.sourceFiniteDonor‖ ≤ 1 :=
    (pc_observable_norm _).trans finiteNorm
  have compared := original_positive_reference_error (pcObservable Supply.sourceFiniteDonor)
    (pc_observable_hermitian _ Supply.finite_donor_positive.isHermitian)
  rw [finite_high_reference,pc_observable_energy] at compared
  have scalarError : |energy Supply.sourceFiniteDonor rho11-positiveHighRead| ≤ (1/1000 : ℝ) :=
    compared.trans ((mul_le_mul_of_nonneg_left observableNorm (by norm_num)).trans (by norm_num))
  have donorError : |energy Source.donor rho11-energy Supply.sourceFiniteDonor rho11| ≤ (1/10^9 : ℝ) := by
    rw [energy_difference]
    exact (energy_abs_le_norm _ rho11 rho11_positive rho11_trace).trans Supply.original_finite_donor_error
  have tri := abs_sub_le (energy Source.donor rho11) (energy Supply.sourceFiniteDonor rho11) positiveHighRead
  linarith only [tri,donorError,scalarError]

open Propagation.Interface Contraction NetContraction

theorem high_observable_preserves :
    Preserves Sectors.pointerOrbit (pcObservable Donor.calculatedDonor) := by
  have pc : Preserves pcOrbit Donor.calculatedDonor := preserves_diagonal _ _
  have full : Preserves Sectors.reservoirOrbit (Post.pcLift Donor.calculatedDonor) :=
    preserves_tensor_left (preserves_relabel (preserves_tensor pc (preserves_one pcOrbit))
      (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))) _
  exact Sectors.fromBlocks_preserves _ _ _ _ full (preserves_zero _) (preserves_zero _) full

theorem high_observable_positive : (pcObservable Donor.calculatedDonor).PosSemidef := by
  have h : (Post.pcLift Donor.calculatedDonor).PosSemidef :=
    ((Spectrum.basisPure_positive _).kronecker Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one
  exact Matrix.nonneg_iff_posSemidef.mp (map_nonneg pointerDiagonal h.nonneg)

theorem reference_word_preserves : Preserves Sectors.pointerOrbit referenceWord :=
  preserves_mul (preserves_mul NetContraction.eleven_preserves NetContraction.pointer_preserves)
    (Sectors.fromBlocks_preserves _ _ _ _ NetContraction.supply_preserves
      (preserves_zero _) (preserves_zero _) NetContraction.supply_preserves)

def highInputObservable : LoadedJoint :=
  star LoadExecution.receivedWord * wordReadout referenceWord (pcObservable Donor.calculatedDonor) *
    LoadExecution.receivedWord

theorem high_input_positive : highInputObservable.PosSemidef := by
  have pulled := high_observable_positive.conjTranspose_mul_mul_same referenceWord
  have read : (wordReadout referenceWord (pcObservable Donor.calculatedDonor)).PosSemidef := by
    simpa only [wordReadout,Supply.donorSlice,Prepared.pointerReadout,Matrix.star_eq_conjTranspose] using
      (pulled.submatrix Sum.inl).submatrix (fun i : PairController × Fin 2 => ((i.1,Supply.donorIndex),i.2))
  exact read.conjTranspose_mul_mul_same LoadExecution.receivedWord

theorem high_input_preserves : Preserves pceOrbit highInputObservable :=
  sandwich_preserves NetContraction.received_preserves
    (donor_slice_preserves _ (pointer_readout_preserves _
      (sandwich_preserves reference_word_preserves high_observable_preserves)))

def highSector (k : Sym2 Basis) : ℝ :=
  energy (restrict pceOrbit k highInputObservable) (restrict pceOrbit k positiveReferenceInput)

theorem high_sector_nonnegative (k : Sym2 Basis) : 0 ≤ highSector k :=
  QuadraticEnergy.positive_energy _ _ (high_input_positive.submatrix Subtype.val)
    (positive_reference_input.submatrix Subtype.val)

theorem high_read_sum : positiveHighRead = ∑ k : Sym2 Basis, highSector k := by
  rw [positiveHighRead,positiveReceivedBody,input_pullback]
  exact energy_eq_sum_restrict high_input_preserves _

def localHighReadout (k : Sym2 Basis) (O : PointerJoint) : Matrix (BodyFiber k) (BodyFiber k) ℂ :=
  (star (NetContraction.localSupply k) *
    (star (NetContraction.localPointer k) *
      (star (NetContraction.localEleven k) * restrict Sectors.pointerOrbit (donorSector k) O *
        NetContraction.localEleven k) * NetContraction.localPointer k).submatrix (insertPointer k) (insertPointer k) *
    NetContraction.localSupply k).submatrix (insertDonor k) (insertDonor k)

theorem local_high_readout_exact (k : Sym2 Basis) (O : PointerJoint) :
    restrict pceOrbit k (wordReadout referenceWord O) = localHighReadout k O := by
  rw [wordReadout,referenceWord,word_corner,donor_restriction,
    restriction_pullback NetContraction.supply_preserves,pointer_restriction,
    restriction_pullback NetContraction.pointer_preserves,
    restriction_pullback NetContraction.eleven_preserves]
  rfl

private theorem reindex_pullback {ι ν : Type*} [Fintype ι] [Fintype ν]
    (e : ν ≃ ι) (A O : Matrix ι ι ℂ) :
    (star A*O*A).submatrix e e=star (A.submatrix e e)*O.submatrix e e*A.submatrix e e := by
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,← Matrix.submatrix_mul_equiv _ _ e e e]
  rfl

private theorem reindex_injection {ι η ν σ : Type*} (M : Matrix ι ι ℂ)
    (inject : η → ι) (body : σ → η) (full : ν → ι) (insert : σ → ν)
    (incidence : ∀ i, full (insert i)=inject (body i)) :
    (M.submatrix inject inject).submatrix body body=(M.submatrix full full).submatrix insert insert := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [incidence i,incidence j]

def coordinateHigh {δ : Type*} (k : Sym2 Basis) (full : δ ≃ FullFiber k) (O : PointerJoint) :=
  (restrict Sectors.pointerOrbit (donorSector k) O).submatrix
    (NetContraction.coordinatePointer k full) (NetContraction.coordinatePointer k full)

theorem coordinate_high_readout {β δ : Type*} [Fintype β] [Fintype δ]
    (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) (O : PointerJoint) :
    (localHighReadout k O).submatrix body body =
      (NetContraction.sourceColumns k full insert)ᴴ *
        (star ((NetContraction.localEleven k).submatrix (NetContraction.coordinatePointer k full)
          (NetContraction.coordinatePointer k full)) * coordinateHigh k full O *
          (NetContraction.localEleven k).submatrix (NetContraction.coordinatePointer k full)
            (NetContraction.coordinatePointer k full)) * NetContraction.sourceColumns k full insert := by
  rw [localHighReadout,reindex_injection _ _ body full insert incidence,reindex_pullback,
    NetContraction.coordinate_corner_exact,reindex_pullback,reindex_pullback,
    column_pullback,column_pullback]
  exact rectangular_pullback _ _ _

theorem coordinate_high_input {β δ : Type*} [Fintype β] [Fintype δ]
    (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) :
    (restrict pceOrbit k highInputObservable).submatrix body body =
      (NetContraction.elevenColumns k body full insert)ᴴ * coordinateHigh k full (pcObservable Donor.calculatedDonor) *
        NetContraction.elevenColumns k body full insert := by
  rw [highInputObservable,restriction_pullback NetContraction.received_preserves,
    local_high_readout_exact,reindex_pullback,coordinate_high_readout k body full insert incidence]
  simp only [Matrix.star_eq_conjTranspose]
  rw [rectangular_pullback,rectangular_pullback]
  have columns :
      (NetContraction.localEleven k).submatrix (NetContraction.coordinatePointer k full)
        (NetContraction.coordinatePointer k full) *
        (NetContraction.sourceColumns k full insert *
          (NetContraction.localReceivedWord k).submatrix body body) =
        NetContraction.elevenColumns k body full insert := by
    rw [NetContraction.coordinate_eleven,NetContraction.coordinate_nine]
    simp only [NetContraction.elevenColumns,NetContraction.nineColumns,
      NetContraction.entranceColumns,Matrix.mul_assoc]
  exact congrArg (fun A => Aᴴ * coordinateHigh k full (pcObservable Donor.calculatedDonor) * A) columns

def firstPC : PointerIndex → PairController := Sum.elim (fun i => i.1.1) (fun i => i.1.1)

private theorem doubled_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) :
    pointerDiagonal (Matrix.diagonal d) = Matrix.diagonal (Sum.elim d d) := by
  ext i j
  rcases i with (i|i) <;> rcases j with (j|j) <;>
    simp [pointerDiagonal,Matrix.diagonal_apply,Matrix.fromBlocks]

private theorem diagonal_tensor_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (d : ι → ℂ) :
    Matrix.kronecker (Matrix.diagonal d) (1 : Matrix κ κ ℂ) = Matrix.diagonal (fun p : ι × κ => d p.1) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases h : i=j <;> by_cases g : k=l <;>
    simp [Matrix.kronecker,Matrix.kroneckerMap_apply,h,g,Prod.mk.injEq]

theorem pc_observable_diagonal (d : PairController → ℂ) :
    pcObservable (Matrix.diagonal d) = Matrix.diagonal (d ∘ firstPC) := by
  rw [pcObservable,Post.pcLift,diagonal_tensor_one,diagonal_tensor_one,doubled_diagonal]
  congr 1
  funext i
  rcases i with (i|i) <;> rfl

def localHighWeight (i : OrdinaryFull ⊕ OrdinaryFull) : ℂ :=
  Sum.elim (fun p => Sum.elim (fun _ => 0) (fun x => if x.2=1 then 1 else 0) p.1)
    (fun p => Sum.elim (fun _ => 0) (fun x => if x.2=1 then 1 else 0) p.1) i

theorem ordinary_coordinate_high (a b : Basis) (ordered : a<b) :
    coordinateHigh (s(a,b)) (ordinaryFullEquiv a b ordered.ne) (pcObservable Donor.calculatedDonor) =
      Matrix.diagonal localHighWeight := by
  rw [Donor.calculatedDonor,Spectrum.basisPure,pc_observable_diagonal]
  unfold coordinateHigh restrict
  rw [Matrix.submatrix_submatrix,Matrix.submatrix_diagonal _ _
    (Subtype.val_injective.comp (NetContraction.coordinatePointer _ _).injective)]
  congr 1
  funext i
  have body_ne (x : Fin 2 × Fin 2) : orbitPC a b x ≠ Supply.donorIndex := by
    intro h
    exact ordinary_ne_donor a b ordered.ne ((Evaluate.ordinary_PC_label a b ordered.ne x).symm.trans
      (congrArg pcOrbit h))
  rcases i with (⟨x,e⟩|⟨x,e⟩) <;> rcases x with (⟨body,c⟩|⟨body,c⟩)
  all_goals change (if _ then (1 : ℂ) else 0) = _
  · change (if orbitPC a b body=Supply.donorIndex then (1 : ℂ) else 0)=0
    rw [if_neg (body_ne body)]
  · change (if ((97,97),c)=((97,97),(1 : Fin 2)) then (1 : ℂ) else 0)=if c=1 then 1 else 0
    simp only [Prod.mk.injEq, true_and]
  · change (if orbitPC a b body=Supply.donorIndex then (1 : ℂ) else 0)=0
    rw [if_neg (body_ne body)]
  · change (if ((97,97),c)=((97,97),(1 : Fin 2)) then (1 : ℂ) else 0)=if c=1 then 1 else 0
    simp only [Prod.mk.injEq, true_and]

theorem local_high_gram {β : Type*} (A : Matrix (OrdinaryFull ⊕ OrdinaryFull) β ℂ) :
    Aᴴ * Matrix.diagonal localHighWeight * A =
      (A.submatrix TopPopulation.highRow id)ᴴ * A.submatrix TopPopulation.highRow id := by
  ext i j
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.submatrix_apply,localHighWeight,TopPopulation.highRow,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two]

theorem positive_reference_ordinary_body (a b : Basis) (distinct : a≠b) :
    (restrict pceOrbit (s(a,b)) positiveReferenceInput).submatrix
      (Scaled.Order.offDiagonalPCEEquiv a b distinct) (Scaled.Order.offDiagonalPCEEquiv a b distinct) =
      Matrix.kronecker (Powered.Dynamics.chargedInput (Field.computedPair.submatrix (pairAddress a b) (pairAddress a b))) environmentState := by
  rw [positiveReferenceInput]
  ext ⟨⟨o,c⟩,e⟩ ⟨⟨p,d⟩,f⟩
  rfl

theorem high_sector_ordinary (a b : Basis) (ordered : a<b) :
    highSector (s(a,b)) = energy (TopPopulation.sourceGram a b ordered)
      (Matrix.kronecker (Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)) environmentState) := by
  rw [highSector,← Input.reindex_energy (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne),
    positive_reference_ordinary_body,coordinate_high_input (s(a,b))
      (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) (ordinaryFullEquiv a b ordered.ne)
      ordinaryInjection (ordinary_donor_injection a b ordered.ne),ordinary_coordinate_high a b ordered,
    charged_environment_energy,rectangular_corner,local_high_gram]
  rw [TopPopulation.sourceGram,TopPopulation.sourceHigh,qvalue_submatrix,ordinary_eleven_columns_value]

theorem high_sector_mid (a : Fin 2) (b : Fin 18) :
    highSector (s(midAnchor a,midPartner b)) =
      energy (TopPopulation.sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b)) (midSectorBody a b) :=
  high_sector_ordinary (midAnchor a) (midPartner b) (mid_address_ordered a b)

theorem reference_high_dominates_mid : TopPopulation.midReferenceHigh ≤ positiveHighRead := by
  classical
  let address (x : Fin 2 × Fin 18) : Sym2 Basis := s(midAnchor x.1,midPartner x.2)
  have injective : Function.Injective address := by
    intro x y h
    rcases Sym2.eq_iff.mp h with h|h
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun z : Basis => z.val) h.1
      · apply Fin.ext
        have same := congrArg Fin.val h.2
        change 6+x.2.val=6+y.2.val at same
        omega
    · have contradiction : midAnchor x.1 < midAnchor x.1 := calc
        midAnchor x.1 < midPartner x.2 := mid_address_ordered x.1 x.2
        _ = midAnchor y.1 := h.2
        _ < midPartner y.2 := mid_address_ordered y.1 y.2
        _ = midAnchor x.1 := h.1.symm
      exact False.elim (lt_irrefl _ contradiction)
  calc
    TopPopulation.midReferenceHigh = ∑ x : Fin 2 × Fin 18, highSector (address x) := by
      rw [Fintype.sum_prod_type]
      simp only [address,high_sector_mid]
      rfl
    _ = ∑ k ∈ Finset.univ.image address, highSector k :=
      (Finset.sum_image (fun x _ y _ h => injective h)).symm
    _ ≤ ∑ k : Sym2 Basis, highSector k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => high_sector_nonnegative k)
    _ = positiveHighRead := high_read_sum.symm

theorem original_top_population_lower : (738/1000 : ℝ) < energy Source.donor rho11 := by
  have reference := TopPopulation.mid_reference_high_lower.trans_le reference_high_dominates_mid
  have error := (abs_le.mp original_top_reference_error).1
  linarith only [reference,error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Population
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
