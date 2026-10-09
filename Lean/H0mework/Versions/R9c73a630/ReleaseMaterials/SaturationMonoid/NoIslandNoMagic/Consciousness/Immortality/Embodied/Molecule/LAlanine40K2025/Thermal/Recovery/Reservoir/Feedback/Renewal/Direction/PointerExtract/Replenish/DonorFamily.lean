import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.DonorTables
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
namespace ReplenishDonor
open Propagation.Interface Contraction Load.Source
open scoped Matrix BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section

theorem mid_donor_source_family (a : Fin 2) (b : Fin 18) :
    sourceDonorGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      donorGramInt (TopPopulation.midTable a b) (midPC a b) := by
  have cols : chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      fromTable (TopPopulation.midTable a b) pointerFin pairFin := by
    rw [← from_to_table (chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b))
      pointerFin pairFin,TopPopulation.mid_table_source]
  simp only [sourceDonorGramInt,sourceRightInt,cols,donorGramInt,rightInt,sourceDonorInt,shiftedDonorInt,donorInt,mid_pc_input_source]

private theorem centeredAt_value (T : IntTable 4 4) (c : Int) :
    value (centeredAt T c)=value (fromTable T pairFin pairFin)-
      ((c : ℝ)/(scale : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases same : i=j
  · subst j; simp [centeredAt,value,raw,scale]; ring
  · simp [centeredAt,value,raw,scale,same]

theorem mid_donor_norm_family (a : Fin 2) (b : Fin 18) :
    ‖value (sourceDonorGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b))-
      (11 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (6/5 : ℝ) := by
  have same : sourceDonorGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      fromTable (midDonorTable a b) pairFin pairFin := by
    rw [mid_donor_source_family,← from_to_table (donorGramInt (TopPopulation.midTable a b) (midPC a b))
      pairFin pairFin,mid_donor_literal]
  rw [same]
  have center := centeredAt_value (midDonorTable a b) (11*scale)
  norm_num [scale] at center
  rw [← center]
  have bound := integer_operator_row_column_bound (centeredAt (midDonorTable a b) (11*scale))
    (6*scale/5) (by norm_num [scale]) (mid_donor_rows a b) (mid_donor_columns a b)
  convert bound using 1 <;> norm_num [scale]

theorem mid_donor_floor_family (a : Fin 2) (b : Fin 18) :
    (979/100 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceDonorGram (midAnchor a) (midPartner b) (mid_address_ordered a b) := by
  have error := donor_gram_error (midAnchor a) (midPartner b) (mid_address_ordered a b)
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (sourceDonorGram (midAnchor a) (midPartner b) (mid_address_ordered a b))
    (value (sourceDonorGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)))
    ((11 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  rw [norm_sub_rev (sourceDonorGram _ _ _) (value _)] at triangle
  have bound := triangle.trans ((add_le_add error (mid_donor_norm_family a b)).trans
    (by norm_num : (1/10^8 : ℝ)+6/5 ≤ 121/100))
  have hermitian : (sourceDonorGram (midAnchor a) (midPartner b) (mid_address_ordered a b)).IsHermitian := by
    have h := Matrix.isHermitian_mul_mul_conjTranspose
      ((sourceRight (midAnchor a) (midPartner b) (mid_address_ordered a b))ᴴ)
      (donor_hermitian (midAnchor a) (midPartner b) (mid_address_ordered a b))
    simpa only [sourceDonorGram,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using h
  have floor := hermitian_lower_from_center _ hermitian 11 (121/100) bound
  convert floor using 1
  norm_num

theorem high_row_injective : Function.Injective rightHighRow := by
  rintro ⟨b,e⟩ ⟨c,f⟩ same
  simp_all [rightHighRow]

def highInt (a b : Basis) (ordered : a < b) := submatrix (sourceRightInt a b ordered) rightHighRow id
def high (a b : Basis) (ordered : a < b) := (sourceRight a b ordered).submatrix rightHighRow id
def highGramInt (a b : Basis) (ordered : a < b) := multiply (adjoint (highInt a b ordered)) (highInt a b ordered)
def highGram (a b : Basis) (ordered : a < b) := (high a b ordered)ᴴ*high a b ordered

theorem high_error (a b : Basis) (ordered : a < b) :
    ‖value (highInt a b ordered)-high a b ordered‖ ≤ (1/10^12 : ℝ) := by
  change ‖(value (sourceRightInt a b ordered)-sourceRight a b ordered).submatrix rightHighRow id‖ ≤ _
  exact (submatrix_rows_norm_le (value (sourceRightInt a b ordered)-sourceRight a b ordered)
    rightHighRow high_row_injective).trans (right_error a b ordered)

theorem high_norm (a b : Basis) (ordered : a < b) : ‖high a b ordered‖ ≤ (24 : ℝ) :=
  (submatrix_rows_norm_le (sourceRight a b ordered) rightHighRow high_row_injective).trans (right_norm a b ordered)

theorem high_gram_error (a b : Basis) (ordered : a < b) :
    ‖value (highGramInt a b ordered)-highGram a b ordered‖ ≤ (1/10^10 : ℝ) := by
  have adj : ‖value (adjoint (highInt a b ordered))-(high a b ordered)ᴴ‖ ≤ (1/10^12 : ℝ) := by
    simpa only [value_adjoint,← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose] using high_error a b ordered
  have adjNorm : ‖(high a b ordered)ᴴ‖ ≤ (24 : ℝ) := by simpa only [Matrix.l2_opNorm_conjTranspose] using high_norm a b ordered
  have bound := rectangular_int_mul_error (adjoint (highInt a b ordered)) (highInt a b ordered)
    ((high a b ordered)ᴴ) (high a b ordered) (by norm_num) (by norm_num) (1/10^12) (1/10^12) adj (high_error a b ordered)
  apply bound.trans
  calc
    _ ≤ (64/10^30 : ℝ)+(1/10^12)*(24+1/10^12)+24*(1/10^12) := by gcongr; exact high_norm a b ordered
    _ ≤ _ := by norm_num

theorem mid_high_source (a : Fin 2) (b : Fin 18) :
    highGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      rightGramInt (TopPopulation.midTable a b) := by
  have cols : chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      fromTable (TopPopulation.midTable a b) pointerFin pairFin := by
    rw [← from_to_table (chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b))
      pointerFin pairFin,TopPopulation.mid_table_source]
  simp only [highGramInt,highInt,sourceRightInt,cols,rightGramInt,rightHighInt,rightInt]

theorem mid_high_norm_family (a : Fin 2) (b : Fin 18) :
    ‖value (highGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b))-
      (1/2 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (1/10000 : ℝ) := by
  have same : highGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)=
      fromTable (midTopTable a b) pairFin pairFin := by
    rw [mid_high_source,← from_to_table (rightGramInt (TopPopulation.midTable a b)) pairFin pairFin,mid_right_top_literal]
  rw [same]
  have center := centeredAt_value (midTopTable a b) (scale/2)
  norm_num [scale] at center
  rw [← center]
  have bound := integer_operator_row_column_bound (centeredAt (midTopTable a b) (scale/2))
    (scale/10000) (by norm_num [scale]) (mid_top_rows a b) (mid_top_columns a b)
  convert bound using 1 <;> norm_num [scale]

theorem mid_high_floor_family (a : Fin 2) (b : Fin 18) :
    (499/1000 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      highGram (midAnchor a) (midPartner b) (mid_address_ordered a b) := by
  have error := high_gram_error (midAnchor a) (midPartner b) (mid_address_ordered a b)
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (highGram (midAnchor a) (midPartner b) (mid_address_ordered a b))
    (value (highGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b)))
    ((1/2 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  rw [norm_sub_rev (highGram _ _ _) (value _)] at triangle
  have bound := triangle.trans ((add_le_add error (mid_high_norm_family a b)).trans
    (by norm_num : (1/10^10 : ℝ)+1/10000 ≤ 1/1000))
  have floor := hermitian_lower_from_center _ (Matrix.isHermitian_conjTranspose_mul_self _)
    (1/2) (1/1000) bound
  change ((1/2-1/1000 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤
    highGram (midAnchor a) (midPartner b) (mid_address_ordered a b) at floor
  convert floor using 1
  norm_num

def swapBodies : Current.FullIndex → Current.FullIndex
  | ((pc,donor),e) => ((donor,pc),e)

theorem ordinary_swap_role (a b : Basis) (different : a ≠ b) (i : OrdinaryFull) :
    (ordinaryFullEquiv a b different (swapRole i)).val=
      swapBodies (ordinaryFullEquiv a b different i).val := by
  rcases i with ⟨i,e⟩
  rcases i with i | i <;> rfl

def donorObservableQ : MatrixQ Current.FullIndex Current.FullIndex :=
  Spec.pcLift.submatrix swapBodies swapBodies

theorem ordinary_donor_source (a b : Basis) (ordered : a < b) :
    donorObservableQ.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      (ordinaryPCFullQ a b).submatrix swapRole swapRole := by
  funext i j
  change Spec.pcLift (swapBodies (ordinaryFullEquiv a b ordered.ne i).val)
    (swapBodies (ordinaryFullEquiv a b ordered.ne j).val)=_
  rw [← ordinary_swap_role,← ordinary_swap_role]
  exact congrFun (congrFun (ordinary_pc_full_source a b ordered) (swapRole i)) (swapRole j)

theorem donor_observable_value : qvalue donorObservableQ=
    Matrix.kronecker (Matrix.kronecker (1 : Matrix PairController PairController ℂ)
      (sourcePCH E)) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [donorObservableQ,qvalue_submatrix,Spec.pcLift_value]
  ext ⟨⟨p,d⟩,e⟩ ⟨⟨p',d'⟩,e'⟩
  simp only [Post.pcLift,Matrix.submatrix_apply,swapBodies,Matrix.kronecker,Matrix.kroneckerMap_apply]
  ring

theorem sourceDonor_actual_restriction (a b : Basis) (ordered : a < b) :
    sourceDonor a b=
      (qvalue donorObservableQ).submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
        (fun i => (ordinaryFullEquiv a b ordered.ne i).val)+(192/5 : ℝ) • 1 := by
  rw [← qvalue_submatrix,ordinary_donor_source a b ordered,qvalue_submatrix]
  rfl

def midDonorRead : ℝ := ∑ a : Fin 2, ∑ b : Fin 18,
  Collision.energy (sourceDonorGram (midAnchor a) (midPartner b) (mid_address_ordered a b)) (midSectorBody a b)

def midTopRead : ℝ := ∑ a : Fin 2, ∑ b : Fin 18,
  Collision.energy (highGram (midAnchor a) (midPartner b) (mid_address_ordered a b)) (midSectorBody a b)

theorem mid_donor_read_lower : (73/10 : ℝ) < midDonorRead := by
  have rows (a : Fin 2) (b : Fin 18) :
      (979/100 : ℝ)*(midSectorBody a b).trace.re ≤
        Collision.energy (sourceDonorGram (midAnchor a) (midPartner b) (mid_address_ordered a b)) (midSectorBody a b) :=
    energy_lower_from_order _ _ (mid_sector_body_positive a b) _ (mid_donor_floor_family a b)
  have lower := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => rows a b))
  change (∑ a : Fin 2, ∑ b : Fin 18, (979/100 : ℝ)*(midSectorBody a b).trace.re) ≤ midDonorRead at lower
  simp_rw [← Finset.mul_sum] at lower
  nlinarith only [lower,mid_sector_body_mass_lower]

theorem mid_top_read_lower : (372/1000 : ℝ) < midTopRead := by
  have rows (a : Fin 2) (b : Fin 18) :
      (499/1000 : ℝ)*(midSectorBody a b).trace.re ≤
        Collision.energy (highGram (midAnchor a) (midPartner b) (mid_address_ordered a b)) (midSectorBody a b) :=
    energy_lower_from_order _ _ (mid_sector_body_positive a b) _ (mid_high_floor_family a b)
  have lower := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => rows a b))
  change (∑ a : Fin 2, ∑ b : Fin 18, (499/1000 : ℝ)*(midSectorBody a b).trace.re) ≤ midTopRead at lower
  simp_rw [← Finset.mul_sum] at lower
  nlinarith only [lower,mid_sector_body_mass_lower]

end
end ReplenishDonor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
