import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SchurNorm
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
namespace ReplenishDonor
open Propagation.Interface Contraction Load.Source
open scoped Matrix BigOperators MatrixOrder Matrix.Norms.L2Operator

def swapRole : OrdinaryFull → OrdinaryFull
  | (.inl p,e) => (.inr p,e)
  | (.inr p,e) => (.inl p,e)

def rightInt (T : IntTable 64 4) := submatrix (fromTable T pointerFin pairFin) Sum.inr id

def donorInt (T : IntTable 32 32) := submatrix (fromTable T ordinaryFullFin ordinaryFullFin) swapRole swapRole

def shiftedDonorInt (T : IntTable 32 32) : MatrixInt OrdinaryFull OrdinaryFull :=
  ⟨fun i j => (donorInt T).re i j+(if i=j then 192*scale/5 else 0),(donorInt T).im⟩

def donorGramInt (T : IntTable 64 4) (P : IntTable 32 32) :=
  multiply (adjoint (rightInt T)) (multiply (shiftedDonorInt P) (rightInt T))
def midDonorGramTable : IntTable 4 4 := ⟨
⟨#[
  (⟨#[10361932113256497743750105952371,7400933298487103827671794,499999208967059463357998741647,-7400933298487099629992305],by decide⟩ : Vector Int 4),
  (⟨#[7400933298487103827671794,10361932219246585514458830637028,7400933298487099057395798,499999205088743060536356092190],by decide⟩ : Vector Int 4),
  (⟨#[499999208967059463357998741647,7400933298487099057395798,10361932113256497743760227617227,-7400933298487094842961897],by decide⟩ : Vector Int 4),
  (⟨#[-7400933298487099629992305,499999205088743060536356092190,-7400933298487094842961897,10361932219246585514476705243893],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-1907158200278625367482309764,27585320,1907158200278625367467202937],by decide⟩ : Vector Int 4),
  (⟨#[1907158200278625367482309764,0,1907158200278625367467167623,46463579],by decide⟩ : Vector Int 4),
  (⟨#[-27585320,-1907158200278625367467167623,0,1907158200278625367449733312],by decide⟩ : Vector Int 4),
  (⟨#[-1907158200278625367467202937,-46463579,-1907158200278625367449733312,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem mid_donor_gram_literal : toTable (donorGramInt midElevenTable midPCFullTable) pairFin pairFin=midDonorGramTable := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel

def centered : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  let G := fromTable midDonorGramTable pairFin pairFin
  ⟨fun i j => G.re i j-(if i=j then 52*scale/5 else 0),G.im⟩

theorem centered_rows (i : Fin 2 × Fin 2) :
    (∑ j : Fin 2 × Fin 2, (|centered.re i j|+|centered.im i j|)) ≤ 11*scale/20 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem centered_columns (j : Fin 2 × Fin 2) :
    (∑ i : Fin 2 × Fin 2, (|centered.re i j|+|centered.im i j|)) ≤ 11*scale/20 := by
  rcases j with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

noncomputable section

theorem centered_value : value centered=value (fromTable midDonorGramTable pairFin pairFin)-
    (52/5 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases same : i=j
  · subst j; simp [centered,value,raw,scale]; ring
  · simp [centered,value,raw,scale,same]

theorem mid_donor_gram_norm :
    ‖value (donorGramInt midElevenTable midPCFullTable)-
      (52/5 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (11/20 : ℝ) := by
  have same : donorGramInt midElevenTable midPCFullTable=fromTable midDonorGramTable pairFin pairFin := by
    rw [← from_to_table (donorGramInt midElevenTable midPCFullTable) pairFin pairFin,mid_donor_gram_literal]
  rw [same,← centered_value]
  have bound := integer_operator_row_column_bound centered (11*scale/20) (by norm_num [scale]) centered_rows centered_columns
  convert bound using 1
  norm_num [scale]

set_option maxHeartbeats 200000

theorem swapRole_injective : Function.Injective swapRole := by
  rintro ⟨a,e⟩ ⟨b,f⟩ same
  cases a <;> cases b <;> simp_all [swapRole]

def sourceRightInt (a b : Basis) (ordered : a < b) :=
  submatrix (chargedElevenInt a b ordered) Sum.inr id

def sourceRight (a b : Basis) (ordered : a < b) : Matrix OrdinaryFull (Fin 2 × Fin 2) ℂ :=
  (qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)).submatrix Sum.inr id

def sourceDonor (a b : Basis) : Matrix OrdinaryFull OrdinaryFull ℂ :=
  (qvalue (ordinaryPCFullQ a b)).submatrix swapRole swapRole+(192/5 : ℝ) • 1

def sourceDonorInt (a b : Basis) : MatrixInt OrdinaryFull OrdinaryFull :=
  let D := submatrix (quantize (ordinaryPCFullQ a b)) swapRole swapRole
  ⟨fun i j => D.re i j+(if i=j then 192*scale/5 else 0),D.im⟩

def sourceDonorGram (a b : Basis) (ordered : a < b) :=
  (sourceRight a b ordered)ᴴ*(sourceDonor a b*sourceRight a b ordered)

def sourceDonorGramInt (a b : Basis) (ordered : a < b) :=
  multiply (adjoint (sourceRightInt a b ordered))
    (multiply (sourceDonorInt a b) (sourceRightInt a b ordered))

theorem right_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceRightInt a b ordered)-sourceRight a b ordered‖ ≤ (1/10^12 : ℝ) := by
  rw [sourceRightInt,value_submatrix,charged_eleven_original,sourceRight]
  change ‖(value (sourceOrdinaryElevenSelectedInt a b ordered)-
    qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)).submatrix Sum.inr id‖ ≤ _
  exact (submatrix_rows_norm_le
    (value (sourceOrdinaryElevenSelectedInt a b ordered)-qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection))
    Sum.inr Sum.inr_injective).trans (source_ordinary_selected_errors a b ordered).2

theorem right_norm (a b : Basis) (ordered : a < b) : ‖sourceRight a b ordered‖ ≤ (24 : ℝ) :=
  (submatrix_rows_norm_le (qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection))
    Sum.inr Sum.inr_injective).trans (source_ordinary_selected_norms_24 a b ordered).2

theorem donor_int_value (a b : Basis) :
    value (sourceDonorInt a b)=
      (value (quantize (ordinaryPCFullQ a b))).submatrix swapRole swapRole+(192/5 : ℝ) • 1 := by
  ext i j
  by_cases same : i=j
  · subst j; simp [sourceDonorInt,value,raw,submatrix,scale]; ring
  · simp [sourceDonorInt,value,raw,submatrix,scale,same]

theorem donor_error (a b : Basis) :
    ‖value (sourceDonorInt a b)-sourceDonor a b‖ ≤ (1/10^12 : ℝ) := by
  rw [donor_int_value,sourceDonor,add_sub_add_right_eq_sub]
  change ‖(value (quantize (ordinaryPCFullQ a b))-qvalue (ordinaryPCFullQ a b)).submatrix swapRole swapRole‖ ≤ _
  exact ((submatrix_norm_le _ _ _ swapRole_injective swapRole_injective).trans
    (quantize_error _ (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull]))).trans (by norm_num)

theorem donor_norm (a b : Basis) (ordered : a < b) : ‖sourceDonor a b‖ ≤ (128 : ℝ) := by
  have full : ‖qvalue (ordinaryPCFullQ a b)‖ ≤ (89 : ℝ) := by
    have split : qvalue (ordinaryPCFullQ a b)=
        (qvalue (ordinaryPCPointerQ a b)).submatrix Sum.inl Sum.inl := rfl
    rw [split]
    exact (submatrix_norm_le _ _ _ Sum.inl_injective Sum.inl_injective).trans (source_ordinary_pc_norm a b ordered)
  have perm := (submatrix_norm_le (qvalue (ordinaryPCFullQ a b)) _ _ swapRole_injective swapRole_injective).trans full
  unfold sourceDonor
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_one]
  norm_num
  linarith only [perm]

theorem donor_hermitian (a b : Basis) (ordered : a < b) : (sourceDonor a b).IsHermitian := by
  have full : (qvalue (ordinaryPCFullQ a b)).IsHermitian := by
    have ptr : (qvalue (ordinaryPCPointerQ a b)).IsHermitian := by
      rw [← ordinary_pc_pointer_source a b ordered,qvalue_submatrix,Spec.pcObservable_value]
      exact Post.finite_PC_observable_hermitian.submatrix _
    exact ptr.submatrix Sum.inl
  exact (full.submatrix swapRole).add ((Matrix.isHermitian_one).smul (show IsSelfAdjoint (192/5 : ℝ) from rfl))

theorem donor_gram_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceDonorGramInt a b ordered)-sourceDonorGram a b ordered‖ ≤ (1/10^8 : ℝ) := by
  have weighted : ‖value (multiply (sourceDonorInt a b) (sourceRightInt a b ordered))-
      sourceDonor a b*sourceRight a b ordered‖ ≤ (2/10^10 : ℝ) := by
    have bound := rectangular_int_mul_error (sourceDonorInt a b) (sourceRightInt a b ordered)
      (sourceDonor a b) (sourceRight a b ordered)
      (by norm_num [OrdinaryFull]) (by norm_num) (1/10^12) (1/10^12)
      (donor_error a b) (right_error a b ordered)
    apply bound.trans
    calc
      _ ≤ (64/10^30 : ℝ)+(1/10^12)*(24+1/10^12)+128*(1/10^12) := by
        gcongr
        · exact right_norm a b ordered
        · exact donor_norm a b ordered
      _ ≤ _ := by norm_num
  have adjError : ‖value (adjoint (sourceRightInt a b ordered))-(sourceRight a b ordered)ᴴ‖ ≤ (1/10^12 : ℝ) := by
    simpa only [value_adjoint,← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose] using right_error a b ordered
  have prodNorm : ‖sourceDonor a b*sourceRight a b ordered‖ ≤ (3072 : ℝ) :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul (donor_norm a b ordered) (right_norm a b ordered)
      (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have adjNorm : ‖(sourceRight a b ordered)ᴴ‖ ≤ (24 : ℝ) := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using right_norm a b ordered
  have bound := rectangular_int_mul_error (adjoint (sourceRightInt a b ordered))
    (multiply (sourceDonorInt a b) (sourceRightInt a b ordered))
    ((sourceRight a b ordered)ᴴ) (sourceDonor a b*sourceRight a b ordered)
    (by norm_num) (by norm_num) (1/10^12) (2/10^10) adjError weighted
  apply bound.trans
  calc
    _ ≤ (64/10^30 : ℝ)+(1/10^12)*(3072+2/10^10)+24*(2/10^10) := by gcongr
    _ ≤ _ := by norm_num

theorem mid_donor_source :
    sourceDonorGramInt (0 : Basis) (6 : Basis) (by decide)=donorGramInt midElevenTable midPCFullTable := by
  have cols : chargedElevenInt (0 : Basis) (6 : Basis) (by decide)=fromTable midElevenTable pointerFin pairFin := by
    rw [← from_to_table (chargedElevenInt (0 : Basis) (6 : Basis) (by decide)) pointerFin pairFin,mid_eleven_original_literal]
  simp only [sourceDonorGramInt,sourceRightInt,cols,donorGramInt,rightInt,sourceDonorInt,shiftedDonorInt,donorInt,mid_pc_input_matrix]

theorem mid_donor_gram_floor : (9849/1000 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
    sourceDonorGram (0 : Basis) (6 : Basis) (by decide) := by
  have error := donor_gram_error (0 : Basis) (6 : Basis) (by decide)
  rw [mid_donor_source] at error
  have bound : ‖sourceDonorGram (0 : Basis) (6 : Basis) (by decide)-
      (52/5 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (551/1000 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (sourceDonorGram (0 : Basis) (6 : Basis) (by decide))
      (value (donorGramInt midElevenTable midPCFullTable))
      ((52/5 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    rw [norm_sub_rev (sourceDonorGram _ _ _) (value _)] at triangle
    exact triangle.trans ((add_le_add error mid_donor_gram_norm).trans (by norm_num))
  have hermitian : (sourceDonorGram (0 : Basis) (6 : Basis) (by decide)).IsHermitian := by
    have h := Matrix.isHermitian_mul_mul_conjTranspose
      ((sourceRight (0 : Basis) (6 : Basis) (by decide))ᴴ)
      (donor_hermitian (0 : Basis) (6 : Basis) (by decide))
    simpa only [sourceDonorGram,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using h
  have floor := hermitian_lower_from_center _ hermitian (52/5) (551/1000) bound
  convert floor using 1
  norm_num

end
end ReplenishDonor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
