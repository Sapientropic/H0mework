import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualMixedSourceGrades

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualPreparedMixed
open GaussCoreHilbert GaussYukawaGrade GaussComposite CanonicalGradedMixed CanonicalGradedMixedSource
open CanonicalGradedSpatialKernel CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open CanonicalPhysicalYResolvent FullYSourceCutoffVolterra
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)
open SourceFamilyOperator
open scoped BigOperators Topology InnerProductSpace

-- Actual physical compression, not a replaced same-momentum Hamiltonian.
def physicalTerm (p : PhysicalMomentum) (cut n : ℕ) (t : ℝ) (F : Index) : Op :=
  finitePrefix (compression p F) (cutoff cut) n t

theorem physicalTerm_grade (p : PhysicalMomentum) (cut n : ℕ) (t : ℝ) (F : Index) :
    Homogeneous (physicalTerm p cut n t F) (n:ℤ) := by
  simpa only [Homogeneous,physicalTerm,Int.cast_natCast] using
    finitePrefix_homogeneous _ _ _ (compression_grade p F) (cutoff_raises cut) n t

theorem physical_terminal (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    physicalTerm p cut 56 t F*cutoff cut=0 := by
  have hY : Homogeneous (cutoff cut) 1 := by
    simpa only [Homogeneous,Int.cast_one,one_smul] using cutoff_raises cut
  have h:=homogeneous_mul _ _ _ _ (physicalTerm_grade p cut 56 t F) hY
  apply source_homogeneous_zero _ 57 _ (by norm_num)
  norm_num [Homogeneous] at h ⊢
  exact h

theorem physical_evolution (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    partialEvolution (compression p F) (cutoff cut) 56 t=
      SourceFiniteUnitary.time (compression p F+cutoff cut) t := by
  apply autonomous_evolution_unique _ _ _ (partialEvolution_initial _ _ 56) t
  intro s
  have h:=partialEvolution_derivative (compression p F) (cutoff cut) 56 s
  have terminal := physical_terminal p cut s F
  change finitePrefix (compression p F) (cutoff cut) 56 s*cutoff cut=0 at terminal
  simpa only [mul_smul_comm,terminal,smul_zero,sub_zero] using h

theorem physical_time_sum (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    SourceFiniteUnitary.time (compression p F+cutoff cut) t=
      ∑ n∈Finset.range 57,physicalTerm p cut n t F := by
  rw [←physical_evolution,CanonicalGradedMixed.partial_sum]
  rfl

def wordTerm (cut : ℕ) (A B : Op) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) (i j k : ℕ) : Op :=
  physicalTerm out cut i r F*A*physicalTerm middle cut j s F*B*physicalTerm input cut k t F

theorem wordTerm_grade (cut : ℕ) (A B : Op) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) (i j k : ℕ) :
    Homogeneous (wordTerm cut A B out middle input r s t F i j k) ((i:ℤ)+a+j+b+k) :=
  homogeneous_mul _ _ _ _
    (homogeneous_mul _ _ _ _
      (homogeneous_mul _ _ _ _
        (homogeneous_mul _ _ _ _ (physicalTerm_grade out cut i r F) ha)
        (physicalTerm_grade middle cut j s F)) hb)
    (physicalTerm_grade input cut k t F)

theorem wordTerm_unbalanced (cut : ℕ) (A B : Op) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) (i j k : ℕ) (different : (i:ℤ)+a+j+b+k≠0) :
    gradeZeroProjection*wordTerm cut A B out middle input r s t F i j k*gradeZeroProjection=0 :=
  gradeZero_unbalanced _ _ (wordTerm_grade cut A B a b ha hb out middle input r s t F i j k) different

def fullWord (cut : ℕ) (A B : Op) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) : Op :=
  gradeZeroProjection*SourceFiniteUnitary.time (compression out F+cutoff cut) r*A*
    SourceFiniteUnitary.time (compression middle F+cutoff cut) s*B*
    SourceFiniteUnitary.time (compression input F+cutoff cut) t*gradeZeroProjection

private theorem triple_sum_identity {R : Type*} [Ring R] (S : Finset ℕ)
    (P A B : R) (f g h : ℕ → R) :
    P*(∑ i ∈ S, f i)*A*(∑ j ∈ S, g j)*B*(∑ k ∈ S, h k)*P=
      ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, P*(f i*A*g j*B*h k)*P := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem fullWord_sum (cut : ℕ) (A B : Op) (out middle input : PhysicalMomentum) (r s t : ℝ) (F : Index) :
    fullWord cut A B out middle input r s t F=
      ∑ i ∈ Finset.range 57, ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57,
        gradeZeroProjection*wordTerm cut A B out middle input r s t F i j k*gradeZeroProjection := by
  dsimp only [fullWord]
  rw [physical_time_sum, physical_time_sum, physical_time_sum]
  exact triple_sum_identity (Finset.range 57) gradeZeroProjection A B
    (fun i => physicalTerm out cut i r F) (fun j => physicalTerm middle cut j s F) (fun k => physicalTerm input cut k t F)

private theorem sum57_to3 {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (vanishes : ∀ n, 3 ≤ n → n<57 → f n=0) :
    ∑ n ∈ Finset.range 57, f n=∑ n ∈ Finset.range 3, f n := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hout
  exact vanishes n (by simpa only [Finset.mem_range, not_lt] using hout)
    (by simpa only [Finset.mem_range] using hn)

def selectedWord (cut : ℕ) (A B : Op) (a b : ℤ) (out middle input : PhysicalMomentum) (r s t : ℝ) (F : Index) : Operator :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
    if (i : ℤ)+a+j+b+k=0 then gradeZeroProjection*wordTerm cut A B out middle input r s t F i j k*gradeZeroProjection else 0

theorem fullWord_selected (cut : ℕ) (A B : Op) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (lowerA : -1≤a) (lowerB : -1≤b)
    (out middle input : PhysicalMomentum) (r s t : ℝ) (F : Index) :
    fullWord cut A B out middle input r s t F=selectedWord cut A B a b out middle input r s t F := by
  let term := fun i j k => gradeZeroProjection*wordTerm cut A B out middle input r s t F i j k*gradeZeroProjection
  have large (i j k : ℕ) (outside : 3 ≤ i ∨ 3 ≤ j ∨ 3 ≤ k) : term i j k=0 :=
    wordTerm_unbalanced cut A B a b ha hb out middle input r s t F i j k (by omega)
  have trimK (i j : ℕ) : (∑ k ∈ Finset.range 57, term i j k)=∑ k ∈ Finset.range 3, term i j k :=
    sum57_to3 (fun k => term i j k) (fun k hk _ => large i j k (Or.inr (Or.inr hk)))
  have trimJ (i : ℕ) : (∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)=
      ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3, term i j k := by
    rw [sum57_to3 (fun j => ∑ k ∈ Finset.range 57, term i j k) (fun j hj _ =>
      Finset.sum_eq_zero (fun k _ => large i j k (Or.inr (Or.inl hj))))]
    exact Finset.sum_congr rfl (fun j _ => trimK i j)
  rw [fullWord_sum]
  change (∑ i ∈ Finset.range 57, ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)=_
  rw [sum57_to3 (fun i => ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)
    (fun i hi _ => Finset.sum_eq_zero (fun j _ =>
      Finset.sum_eq_zero (fun k _ => large i j k (Or.inl hi))))]
  unfold selectedWord
  apply Finset.sum_congr rfl
  intro i _
  rw [trimJ]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with balanced
  · rfl
  · exact wordTerm_unbalanced cut A B a b ha hb out middle input r s t F i j k balanced



theorem wordTerm_bound (cut : ℕ) (A B : Op) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) (i j k : ℕ) :
    ‖gradeZeroProjection*wordTerm cut A B out middle input r s t F i j k*gradeZeroProjection‖ ≤
      ‖A‖*‖B‖*((|r| *‖cutoff cut‖)^i*(|s| *‖cutoff cut‖)^j*(|t| *‖cutoff cut‖)^k) := by
  unfold wordTerm
  calc
    _ ≤ ‖gradeZeroProjection‖*(‖physicalTerm out cut i r F‖*‖A‖*
        ‖physicalTerm middle cut j s F‖*‖B‖*‖physicalTerm input cut k t F‖)*‖gradeZeroProjection‖ := by
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact norm_mul_le _ _
    _ ≤ 1*((|r| *‖cutoff cut‖)^i*‖A‖*(|s| *‖cutoff cut‖)^j*‖B‖*(|t| *‖cutoff cut‖)^k)*1 := by
      gcongr
      · exact gradeZero_norm
      · exact finitePrefix_bound _ _ (compression_selfAdjoint out F) i r
      · exact finitePrefix_bound _ _ (compression_selfAdjoint middle F) j s
      · exact finitePrefix_bound _ _ (compression_selfAdjoint input F) k t
      · exact gradeZero_norm
    _ = _ := by ring

theorem selectedWord_bound (cut : ℕ) (A B : Op) (a b : ℤ) (out middle input : PhysicalMomentum)
    (r s t : ℝ) (F : Index) :
    ‖selectedWord cut A B a b out middle input r s t F‖≤
      ‖A‖*‖B‖*CanonicalGradedMixedReturn.pathBound cut a b r s t := by
  unfold selectedWord CanonicalGradedMixedReturn.pathBound
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · exact wordTerm_bound cut A B out middle input r s t F i j k
  · simp only [norm_zero,mul_zero,le_refl]

def bandFamily (cut : ℕ) (a b : SourceScalarFock.ScalarIndex) (A B : NativeCurrent)
    (i j : Fin 3) (out middle input : PhysicalMomentum) (r s t : ℝ) :
    SourceFamilyOperator.Operator Index H where
  component F := fullWord cut (actualBand a A i) (actualBand b B j) out middle input r s t F
  bounded := ⟨‖actualBand a A i‖*‖actualBand b B j‖*
      CanonicalGradedMixedReturn.pathBound cut (bandGrade i) (bandGrade j) r s t,
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (CanonicalGradedMixedReturn.pathBound_nonnegative cut (bandGrade i) (bandGrade j) r s t),
    fun F x=>by
      have normBound:=selectedWord_bound cut (actualBand a A i) (actualBand b B j)
        (bandGrade i) (bandGrade j) out middle input r s t F
      rw [←fullWord_selected cut _ _ _ _ (actualBand_grade a A i) (actualBand_grade b B j)
        (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F] at normBound
      exact ((fullWord cut _ _ out middle input r s t F).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right normBound (norm_nonneg x))⟩

def completedBandWord (cut : ℕ) (a b : SourceScalarFock.ScalarIndex) (A B : NativeCurrent)
    (i j : Fin 3) (out middle input : PhysicalMomentum) (r s t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (bandFamily cut a b A B i j out middle input r s t)


theorem actual_reader_paths (cut : ℕ) (a b : SourceScalarFock.ScalarIndex) (A B : NativeCurrent)
    (out middle input : PhysicalMomentum) (r s t : ℝ) (F : Index) :
    fullWord cut (actualReader a A) (actualReader b B) out middle input r s t F=
      ∑ i : Fin 3, ∑ j : Fin 3,selectedWord cut (actualBand a A i) (actualBand b B j)
        (bandGrade i) (bandGrade j) out middle input r s t F := by
  have split : fullWord cut (actualReader a A) (actualReader b B) out middle input r s t F=
      ∑ i : Fin 3, ∑ j : Fin 3,fullWord cut (actualBand a A i) (actualBand b B j) out middle input r s t F := by
    simp only [actualReader,fullWord,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [split]
  exact Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>
    fullWord_selected cut _ _ _ _ (actualBand_grade a A i) (actualBand_grade b B j)
      (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F))

theorem completedBandWord_bound (cut : ℕ) (a b : SourceScalarFock.ScalarIndex) (A B : NativeCurrent)
    (i j : Fin 3) (out middle input : PhysicalMomentum) (r s t : ℝ) :
    ‖completedBandWord cut a b A B i j out middle input r s t‖≤
      ‖actualBand a A i‖*‖actualBand b B j‖*CanonicalGradedMixedReturn.pathBound cut (bandGrade i) (bandGrade j) r s t := by
  apply CanonicalGradedVariation.lift_bound sourceFilter
    (bandFamily cut a b A B i j out middle input r s t) _
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (CanonicalGradedMixedReturn.pathBound_nonnegative cut (bandGrade i) (bandGrade j) r s t))
  intro F
  change ‖fullWord cut _ _ out middle input r s t F‖≤_
  rw [fullWord_selected cut _ _ _ _ (actualBand_grade a A i) (actualBand_grade b B j)
    (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F]
  exact selectedWord_bound cut _ _ _ _ out middle input r s t F

end LowEnergy.PreparationVacuumActualPreparedMixed
