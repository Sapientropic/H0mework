import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Bounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.DonorFamily
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Readout
open Collision Quantum Resource Propagation.Interface Propagation.Producer Load.Source
open Blocks Blocks.EnergyFrame Inverse.Scaled.Finite Inverse.Scaled.Finite.Evaluation
open NetContraction.Fixed Contraction
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def rightBlock {ι : Type*} (M : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 0 0 M

theorem right_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (positive : M.PosSemidef) : (rightBlock M).PosSemidef := by
  have pair : (0 : Matrix ι ι ℂ × Matrix ι ι ℂ) ≤ (0,M) := ⟨le_rfl,positive.nonneg⟩
  exact Matrix.nonneg_iff_posSemidef.mp (map_nonneg Inverse.twoBlockEmbedding pair)

theorem right_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : ‖rightBlock M‖ ≤ ‖M‖ := by
  have bound := Inverse.two_block_norm (0 : Matrix ι ι ℂ) M
  simpa only [rightBlock,norm_zero,max_eq_right (norm_nonneg M)] using bound

def donorFull : Current.FullJoint :=
  Matrix.kronecker (Matrix.kronecker (1 : Matrix PairController PairController ℂ)
    (sourcePCH E+(192/5 : ℝ) • 1)) (1 : Matrix (Fin 2) (Fin 2) ℂ)
def donorObservable : PointerJoint := rightBlock donorFull
def topObservable : PointerJoint := rightBlock (Post.pcLift Donor.calculatedDonor)

theorem donor_full_positive : donorFull.PosSemidef :=
  (Matrix.PosSemidef.one.kronecker Replenish.Bounds.calculated_shift_positive).kronecker Matrix.PosSemidef.one
theorem donor_positive : donorObservable.PosSemidef := right_positive donorFull donor_full_positive
theorem top_positive : topObservable.PosSemidef := right_positive _
  (((Spectrum.basisPure_positive _).kronecker Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one)

theorem donor_full_value : donorFull=qvalue ReplenishDonor.donorObservableQ+(192/5 : ℝ) • 1 := by
  rw [ReplenishDonor.donor_observable_value]
  simp only [donorFull,Matrix.kronecker,Matrix.kronecker_add,Matrix.add_kronecker,Matrix.kronecker_smul,
    Matrix.smul_kronecker,Matrix.one_kronecker_one]

theorem donor_norm : ‖donorObservable‖ ≤ (128 : ℝ) := by
  have shifted : ‖sourcePCH E+(192/5 : ℝ) • (1 : Matrix PairController PairController ℂ)‖ ≤ (128 : ℝ) := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_one,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 192/5),mul_one]
    linarith only [Inverse.numeric_PC_norm]
  have body := NonUnitalStarAlgHom.norm_apply_le (Load.Producer.StrictThermal.tensorRight (ι := PairController) (κ := PairController))
    (sourcePCH E+(192/5 : ℝ) • 1)
  have full := NonUnitalStarAlgHom.norm_apply_le (Load.Producer.StrictThermal.tensorLeft (ι := PairController × PairController) (κ := Fin 2))
    (Matrix.kronecker (1 : Matrix PairController PairController ℂ) (sourcePCH E+(192/5 : ℝ) • 1))
  exact (right_norm donorFull).trans (full.trans (body.trans shifted))

theorem top_norm : ‖topObservable‖ ≤ (1 : ℝ) := by
  exact (right_norm _).trans ((Post.pc_lift_norm _).trans
    (by
      rw [Donor.calculatedDonor,Spectrum.basisPure,Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      split_ifs <;> norm_num))

theorem right_preserves (M : Current.FullJoint) (kept : Preserves Sectors.reservoirOrbit M) :
    Preserves Sectors.pointerOrbit (rightBlock M) :=
  Sectors.fromBlocks_preserves _ _ _ _ (preserves_zero _) (preserves_zero _) (preserves_zero _) kept

theorem donor_preserves : Preserves Sectors.pointerOrbit donorObservable := by
  apply right_preserves
  have h := preserves_add numeric_pc_preserves
    (preserves_smul (preserves_one pcOrbit) (192/5 : ℝ))
  exact preserves_tensor_left
    (preserves_relabel (preserves_tensor (preserves_one pcOrbit) h)
      (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))) _

theorem top_preserves : Preserves Sectors.pointerOrbit topObservable := by
  apply right_preserves
  have pc : Preserves pcOrbit Donor.calculatedDonor := preserves_diagonal _ _
  exact preserves_tensor_left (preserves_relabel (preserves_tensor pc (preserves_one pcOrbit))
    (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))) _

def referenceRead (O : PointerJoint) : ℝ :=
  energy (Population.wordReadout Population.referenceWord O) Population.positiveReceivedBody

def inputObservable (O : PointerJoint) : LoadedJoint :=
  star LoadExecution.receivedWord * Population.wordReadout Population.referenceWord O * LoadExecution.receivedWord

theorem input_positive (O : PointerJoint) (positive : O.PosSemidef) : (inputObservable O).PosSemidef := by
  have pulled := positive.conjTranspose_mul_mul_same Population.referenceWord
  have read : (Population.wordReadout Population.referenceWord O).PosSemidef := by
    simpa only [Population.wordReadout,Supply.donorSlice,Prepared.pointerReadout,Matrix.star_eq_conjTranspose] using
      (pulled.submatrix Sum.inl).submatrix (fun i : PairController × Fin 2 => ((i.1,Supply.donorIndex),i.2))
  exact read.conjTranspose_mul_mul_same LoadExecution.receivedWord

theorem input_preserves (O : PointerJoint) (kept : Preserves Sectors.pointerOrbit O) :
    Preserves pceOrbit (inputObservable O) :=
  sandwich_preserves NetContraction.received_preserves
    (donor_slice_preserves _ (pointer_readout_preserves _
      (sandwich_preserves Population.reference_word_preserves kept)))

def sectorRead (O : PointerJoint) (k : Sym2 Basis) : ℝ :=
  energy (restrict pceOrbit k (inputObservable O)) (restrict pceOrbit k positiveReferenceInput)

theorem sector_nonnegative (O : PointerJoint) (positive : O.PosSemidef) (k : Sym2 Basis) :
    0 ≤ sectorRead O k := QuadraticEnergy.positive_energy _ _
      ((input_positive O positive).submatrix Subtype.val) (positive_reference_input.submatrix Subtype.val)

theorem reference_sum (O : PointerJoint) (kept : Preserves Sectors.pointerOrbit O) :
    referenceRead O=∑ k : Sym2 Basis, sectorRead O k := by
  classical
  rw [referenceRead,Population.positiveReceivedBody,NetContraction.input_pullback]
  exact energy_eq_sum_restrict (input_preserves O kept) _

open NetContraction Population

private theorem reindex_pullback {ι ν : Type*} [Fintype ι] [Fintype ν]
    (e : ν ≃ ι) (A O : Matrix ι ι ℂ) :
    (star A*O*A).submatrix e e=star (A.submatrix e e)*O.submatrix e e*A.submatrix e e := by
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,← Matrix.submatrix_mul_equiv _ _ e e e]
  rfl

theorem coordinate_input {β δ : Type*} [Fintype β] [Fintype δ]
    (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) (O : PointerJoint) :
    (restrict pceOrbit k (inputObservable O)).submatrix body body =
      (NetContraction.elevenColumns k body full insert)ᴴ * coordinateHigh k full O *
        NetContraction.elevenColumns k body full insert := by
  rw [inputObservable,restriction_pullback NetContraction.received_preserves,
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
  exact congrArg (fun A => Aᴴ * coordinateHigh k full O * A) columns


theorem coordinate_right (k : Sym2 Basis) {δ : Type*} (full : δ ≃ FullFiber k)
    (M : Current.FullJoint) :
    coordinateHigh k full (rightBlock M)=rightBlock (M.submatrix (fun i => (full i).val) (fun i => (full i).val)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem donor_coordinate (a b : Basis) (ordered : a < b) :
    coordinateHigh (s(a,b)) (ordinaryFullEquiv a b ordered.ne) donorObservable=
      rightBlock (ReplenishDonor.sourceDonor a b) := by
  rw [donorObservable,coordinate_right,donor_full_value,ReplenishDonor.sourceDonor_actual_restriction a b ordered]
  simp only [Matrix.submatrix_add,Matrix.submatrix_smul,Pi.add_apply,Pi.smul_apply]
  have identity : (1 : Current.FullJoint).submatrix
      (fun i : OrdinaryFull => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i : OrdinaryFull => (ordinaryFullEquiv a b ordered.ne i).val)=(1 : Matrix OrdinaryFull OrdinaryFull ℂ) :=
    Matrix.submatrix_one _ (Subtype.val_injective.comp (ordinaryFullEquiv a b ordered.ne).injective)
  rw [identity]

theorem right_gram {ι β : Type*} [Fintype ι] (A : Matrix (ι ⊕ ι) β ℂ) (D : Matrix ι ι ℂ) :
    Aᴴ*rightBlock D*A=(A.submatrix Sum.inr id)ᴴ*D*(A.submatrix Sum.inr id) := by
  ext i j
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,rightBlock,
    Matrix.fromBlocks,Fintype.sum_sum_type]

theorem donor_sector (a b : Basis) (ordered : a < b) :
    sectorRead donorObservable (s(a,b))=energy (ReplenishDonor.sourceDonorGram a b ordered)
      (Matrix.kronecker (Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)) environmentState) := by
  rw [sectorRead,← Input.reindex_energy (Inverse.Scaled.Order.offDiagonalPCEEquiv a b ordered.ne),
    positive_reference_ordinary_body,coordinate_input (s(a,b))
      (Inverse.Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) (ordinaryFullEquiv a b ordered.ne)
      ordinaryInjection (ordinary_donor_injection a b ordered.ne),donor_coordinate a b ordered,
    charged_environment_energy,rectangular_corner,right_gram]
  rw [ReplenishDonor.sourceDonorGram,ReplenishDonor.sourceRight,qvalue_submatrix,ordinary_eleven_columns_value]
  simp only [Matrix.mul_assoc]

def topWeight (p : OrdinaryFull) : ℂ :=
  Sum.elim (fun _ => 0) (fun x => if x.2=1 then 1 else 0) p.1

theorem top_coordinate (a b : Basis) (ordered : a < b) :
    coordinateHigh (s(a,b)) (ordinaryFullEquiv a b ordered.ne) topObservable=
      rightBlock (Matrix.diagonal topWeight) := by
  rw [topObservable,coordinate_right]
  apply congrArg rightBlock
  have coordinate := ordinary_coordinate_high a b ordered
  have same := congrArg (fun M => M.submatrix Sum.inr Sum.inr) coordinate
  rw [Matrix.submatrix_diagonal _ _ Sum.inr_injective] at same
  exact same

theorem top_gram {β : Type*} (A : Matrix OrdinaryFull β ℂ) :
    Aᴴ*Matrix.diagonal topWeight*A=
      (A.submatrix ReplenishDonor.rightHighRow id)ᴴ*A.submatrix ReplenishDonor.rightHighRow id := by
  ext i j
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,topWeight,
    ReplenishDonor.rightHighRow,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two]

theorem top_sector (a b : Basis) (ordered : a < b) :
    sectorRead topObservable (s(a,b))=energy (ReplenishDonor.highGram a b ordered)
      (Matrix.kronecker (Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)) environmentState) := by
  rw [sectorRead,← Input.reindex_energy (Inverse.Scaled.Order.offDiagonalPCEEquiv a b ordered.ne),
    positive_reference_ordinary_body,coordinate_input (s(a,b))
      (Inverse.Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) (ordinaryFullEquiv a b ordered.ne)
      ordinaryInjection (ordinary_donor_injection a b ordered.ne),top_coordinate a b ordered,
    charged_environment_energy,rectangular_corner,right_gram,top_gram]
  rw [ReplenishDonor.highGram,ReplenishDonor.high,ReplenishDonor.sourceRight,
    qvalue_submatrix,ordinary_eleven_columns_value]

theorem reference_dominates_mid (O : PointerJoint) (positive : O.PosSemidef)
    (kept : Preserves Sectors.pointerOrbit O) :
    (∑ a : Fin 2, ∑ b : Fin 18, sectorRead O (s(midAnchor a,midPartner b))) ≤ referenceRead O := by
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
    _ = ∑ x : Fin 2 × Fin 18, sectorRead O (address x) := by rw [Fintype.sum_prod_type]
    _ = ∑ k ∈ Finset.univ.image address, sectorRead O k :=
      (Finset.sum_image (fun x _ y _ h => injective h)).symm
    _ ≤ ∑ k : Sym2 Basis, sectorRead O k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => sector_nonnegative O positive k)
    _ = referenceRead O := (reference_sum O kept).symm

theorem donor_reference_lower : (73/10 : ℝ) < referenceRead donorObservable := by
  have lower := reference_dominates_mid donorObservable donor_positive donor_preserves
  simp_rw [donor_sector _ _ (mid_address_ordered _ _)] at lower
  exact ReplenishDonor.mid_donor_read_lower.trans_le lower

theorem top_reference_lower : (372/1000 : ℝ) < referenceRead topObservable := by
  have lower := reference_dominates_mid topObservable top_positive top_preserves
  simp_rw [top_sector _ _ (mid_address_ordered _ _)] at lower
  exact ReplenishDonor.mid_top_read_lower.trans_le lower

def originalObservable (O : PointerJoint) : PointerJoint :=
  conjugation (star Post.pointerFrame) O

private theorem conjugation_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    conjugation U (conjugation (star U) O)=O := by
  change Unitary.conjStarAlgAut ℂ _ U (Unitary.conjStarAlgAut ℂ _ (star U) O)=O
  rw [← Unitary.conjStarAlgAut_symm]
  exact StarAlgEquiv.apply_symm_apply _ _

theorem original_reference_error (O : PointerJoint) (hO : O.IsHermitian) :
    |energy (originalObservable O) Weak.execution.joint-referenceRead O| ≤ (1/1000 : ℝ)*‖O‖ := by
  have bounded := Population.original_positive_reference_error (originalObservable O)
    (Prepared.conjugation_hermitian _ _ hO)
  have restored : conjugation Post.pointerFrame (originalObservable O)=O := conjugation_inverse _ _
  have normO : ‖originalObservable O‖=‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint (star Post.pointerFrame)) O
  rw [normO,Population.positiveReferenceRead,restored] at bounded
  exact bounded

theorem original_donor_reference_lower :
    (717/100 : ℝ) < energy (originalObservable donorObservable) Weak.execution.joint := by
  have error := (original_reference_error donorObservable donor_positive.isHermitian).trans
    (mul_le_mul_of_nonneg_left donor_norm (by norm_num))
  linarith only [(abs_le.mp error).1,donor_reference_lower]

theorem original_top_reference_lower :
    (371/1000 : ℝ) < energy (originalObservable topObservable) Weak.execution.joint := by
  have error := (original_reference_error topObservable top_positive.isHermitian).trans
    (mul_le_mul_of_nonneg_left top_norm (by norm_num))
  linarith only [(abs_le.mp error).1,top_reference_lower]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Readout
