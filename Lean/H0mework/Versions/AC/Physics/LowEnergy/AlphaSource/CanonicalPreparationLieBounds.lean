import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarGuard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseScalar
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeConnectionVariationDensity Stage9C.Material.SpinPair
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SourceQuantumConfigurationHilbert PreparationCoordinates PreparationChartGuard
open scoped BigOperators RealInnerProductSpace

theorem real_abs_sub_le_sum (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)

def actualRawBlock (x : Fin 12 → ℝ) : P286LieBlockData :=
  (⟨!![(x 6 : ℂ)*Complex.I,x 0+x 1*Complex.I,x 2+x 3*Complex.I;
        -x 0+x 1*Complex.I,(x 7 : ℂ)*Complex.I,x 4+x 5*Complex.I;
        -x 2+x 3*Complex.I,-x 4+x 5*Complex.I,-((x 6+x 7 : ℝ) : ℂ)*Complex.I],by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_succ]; ring⟩,
   ⟨!![(x 10 : ℂ)*Complex.I,x 8+x 9*Complex.I;
        -x 8+x 9*Complex.I,-(x 10 : ℂ)*Complex.I],by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_succ]⟩,
   ⟨(x 11 : ℂ)*Complex.I,by
      change star ((x 11 : ℂ)*Complex.I)=-((x 11 : ℂ)*Complex.I)
      simp⟩)

theorem actual_raw_block_decode (x : Fin 12 → ℝ) :
    rawCoordinates.symm x=p286CoordinateEquiv (actualRawBlock x) := by
  apply rawCoordinates.injective
  rw [rawCoordinates.apply_symm_apply]
  change x=rawRead _
  unfold rawRead
  rw [nativeCoordinates_apply]
  ext i; fin_cases i <;> simp [actualRawBlock]

private def actualRawMother (x : Fin 12 → ℝ) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (actualRawBlock x)

private def actualRawFullMatrix (x : Fin 12 → ℝ) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![x 6*Complex.I,x 0+x 1*Complex.I,x 2+x 3*Complex.I,0,0,0,0;
     -x 0+x 1*Complex.I,x 7*Complex.I,x 4+x 5*Complex.I,0,0,0,0;
     -x 2+x 3*Complex.I,-x 4+x 5*Complex.I,-(x 6+x 7)*Complex.I,0,0,0,0;
     0,0,0,x 10*Complex.I,x 8+x 9*Complex.I,0,0;
     0,0,0,-x 8+x 9*Complex.I,-x 10*Complex.I,0,0;
     0,0,0,0,0,x 11*Complex.I,0;
     0,0,0,0,0,0,-x 11*Complex.I]

private theorem actual_raw_mother_numeric (x : Fin 12 → ℝ) (a b : Fin 7) :
    (actualRawMother x).val (SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7.symm a)
      (SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7.symm b)=
      actualRawFullMatrix x a b := by
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals first
    | (change -((x 6+x 7 : ℝ) : ℂ)*Complex.I=-((x 6 : ℂ)+(x 7 : ℂ))*Complex.I; simp)
    | (change -((x 11 : ℂ)*Complex.I)=-(x 11 : ℂ)*Complex.I; ring)

theorem actual_raw_unit_mother_bound (k : Fin 12) (i j : SU7MotherIndex) :
    ‖(actualRawMother (Pi.single k 1)).val i j‖ ≤ 1 := by
  obtain ⟨a,rfl⟩:=SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7.symm.surjective i
  obtain ⟨b,rfl⟩:=SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.smBlockIndexEquivFin7.symm.surjective j
  rw [actual_raw_mother_numeric]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [actualRawFullMatrix,Pi.single_apply]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem actual_raw_unit_action_bound (i : Fin 12) (sigma : Scalar) :
    ‖action sigma (rawCoordinates.symm (Pi.single i 1))‖ ≤ 117600*‖sigma‖ := by
  rw [actual_raw_block_decode]
  change ‖scalarMotherLieAction (p286LieBlockEmbed
    (p286CoordinateEquiv.symm (p286CoordinateEquiv (actualRawBlock (Pi.single i 1))))) sigma‖ ≤ _
  rw [p286CoordinateEquiv.symm_apply_apply]
  exact scalar_operator_bound _ (actual_raw_unit_mother_bound i) sigma

theorem actual_raw_decomposition (a : NativeLie) :
    a=∑ i : Fin 12, rawCoordinates a i • rawCoordinates.symm (Pi.single i 1) := by
  apply rawCoordinates.injective
  simp only [map_sum,map_smul,LinearEquiv.apply_symm_apply]
  ext j
  simp [Pi.single_apply]

theorem actual_full_scalar_action_bound (a : NativeLie) (sigma : Scalar) :
    ‖action sigma a‖ ≤ 117600*(∑ i : Fin 12, |rawCoordinates a i|)*‖sigma‖ := by
  nth_rw 1 [actual_raw_decomposition a]
  rw [map_sum]
  simp only [map_smul]
  calc
    _ ≤ ∑ i : Fin 12, ‖rawCoordinates a i • action sigma (rawCoordinates.symm (Pi.single i 1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 12, |rawCoordinates a i| * (117600*‖sigma‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (actual_raw_unit_action_bound i sigma) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem complex_pair_bound (r t : ℝ) (M : ℝ) (hr : |r| ≤ M) (ht : |t| ≤ M) :
    ‖(r : ℂ)+(t : ℂ)*Complex.I‖ ≤ 2*M := by
  calc
    _ ≤ ‖(r : ℂ)‖+‖(t : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |r|+|t| := by simp [Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by linarith

theorem actual_raw_color_entry_bound (x : Fin 12 → ℝ) (M : ℝ) (positive : 0 ≤ M)
    (bound : ∀ i,|x i| ≤ M) (i j : Fin 3) : ‖(actualRawBlock x).1.val i j‖ ≤ 2*M := by
  have negative (a b : Fin 12) : ‖-(x a : ℂ)+(x b : ℂ)*Complex.I‖ ≤ 2*M := by
    simpa only [Complex.ofReal_neg] using
      complex_pair_bound (-x a) (x b) M (by simpa only [abs_neg] using bound a) (bound b)
  have sum : |x 6+x 7| ≤ 2*M :=
    (abs_add_le (x 6) (x 7)).trans (show |x 6|+|x 7|≤2*M by linarith [bound 6,bound 7])
  fin_cases i <;> fin_cases j <;> simp only [actualRawBlock]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp -failIfUnchanged only [norm_mul,Complex.norm_I,mul_one,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  all_goals first
    | exact complex_pair_bound _ _ M (bound _) (bound _)
    | exact negative _ _
    | linarith [bound 6,bound 7,bound 10]

theorem actual_raw_weak_entry_bound (x : Fin 12 → ℝ) (M : ℝ) (positive : 0 ≤ M)
    (bound : ∀ i,|x i| ≤ M) (i j : Fin 2) : ‖(actualRawBlock x).2.1.val i j‖ ≤ 2*M := by
  have negative : ‖-(x 8 : ℂ)+(x 9 : ℂ)*Complex.I‖ ≤ 2*M := by
    simpa only [Complex.ofReal_neg] using
      complex_pair_bound (-x 8) (x 9) M (by simpa only [abs_neg] using bound 8) (bound 9)
  fin_cases i <;> fin_cases j <;> simp only [actualRawBlock]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp -failIfUnchanged only [norm_mul,Complex.norm_I,mul_one,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  all_goals first
    | exact complex_pair_bound _ _ M (bound _) (bound _)
    | exact negative
    | linarith [bound 10]

private theorem product_matrix_entry_bound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (M N : ℝ) (positiveM : 0 ≤ M) (_positiveN : 0 ≤ N)
    (boundA : ∀ i j,‖A i j‖ ≤ 2*M) (boundB : ∀ i j,‖B i j‖ ≤ 2*N) (i j : Fin n) :
    ‖(A*B) i j‖ ≤ n*(4*M*N) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin n, ‖A i k*B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, (2*M)*(2*N) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (boundA i k) (boundB k j) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring_nf; simp

theorem actual_raw_bracket_bound (a b : NativeLie) (M N : ℝ)
    (positiveM : 0 ≤ M) (positiveN : 0 ≤ N)
    (boundA : ∀ i,|rawCoordinates a i| ≤ M) (boundB : ∀ i,|rawCoordinates b i| ≤ N) (k : Fin 12) :
    |rawCoordinates (jointP286CoordinateLieBracket a b) k| ≤ 100*M*N := by
  let x:=rawCoordinates a
  let y:=rawCoordinates b
  have decodeA : a=p286CoordinateEquiv (actualRawBlock x) := by
    rw [← actual_raw_block_decode,LinearEquiv.symm_apply_apply]
  have decodeB : b=p286CoordinateEquiv (actualRawBlock y) := by
    rw [← actual_raw_block_decode,LinearEquiv.symm_apply_apply]
  have color (i j : Fin 3) : ‖(p286LieBracket (actualRawBlock x) (actualRawBlock y)).1.val i j‖ ≤ 24*M*N := by
    change ‖((actualRawBlock x).1.val*(actualRawBlock y).1.val-
      (actualRawBlock y).1.val*(actualRawBlock x).1.val) i j‖ ≤ _
    exact (norm_sub_le _ _).trans (by
      have left:=product_matrix_entry_bound _ _ M N positiveM positiveN
        (actual_raw_color_entry_bound x M positiveM boundA) (actual_raw_color_entry_bound y N positiveN boundB) i j
      have right:=product_matrix_entry_bound _ _ N M positiveN positiveM
        (actual_raw_color_entry_bound y N positiveN boundB) (actual_raw_color_entry_bound x M positiveM boundA) i j
      norm_num at left right
      nlinarith)
  have weak (i j : Fin 2) : ‖(p286LieBracket (actualRawBlock x) (actualRawBlock y)).2.1.val i j‖ ≤ 16*M*N := by
    change ‖((actualRawBlock x).2.1.val*(actualRawBlock y).2.1.val-
      (actualRawBlock y).2.1.val*(actualRawBlock x).2.1.val) i j‖ ≤ _
    exact (norm_sub_le _ _).trans (by
      have left:=product_matrix_entry_bound _ _ M N positiveM positiveN
        (actual_raw_weak_entry_bound x M positiveM boundA) (actual_raw_weak_entry_bound y N positiveN boundB) i j
      have right:=product_matrix_entry_bound _ _ N M positiveN positiveM
        (actual_raw_weak_entry_bound y N positiveN boundB) (actual_raw_weak_entry_bound x M positiveM boundA) i j
      norm_num at left right
      nlinarith)
  rw [decodeA,decodeB]
  unfold jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm_apply_apply,p286CoordinateEquiv.symm_apply_apply]
  change |rawRead (p286CoordinateEquiv (p286LieBracket (actualRawBlock x) (actualRawBlock y))) k| ≤ _
  unfold rawRead
  rw [nativeCoordinates_apply]
  have positive:=mul_nonneg positiveM positiveN
  fin_cases k
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  · exact (Complex.abs_re_le_norm _).trans ((color 0 1).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((color 0 1).trans (by nlinarith))
  · exact (Complex.abs_re_le_norm _).trans ((color 0 2).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((color 0 2).trans (by nlinarith))
  · exact (Complex.abs_re_le_norm _).trans ((color 1 2).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((color 1 2).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((color 0 0).trans (by nlinarith))
  · change |-((p286LieBracket (actualRawBlock x) (actualRawBlock y)).1.val 2 2).im -
      ((p286LieBracket (actualRawBlock x) (actualRawBlock y)).1.val 0 0).im| ≤ _
    have first:=(Complex.abs_im_le_norm _).trans (color 2 2)
    have second:=(Complex.abs_im_le_norm _).trans (color 0 0)
    have difference:=real_abs_sub_le_sum
      (-((p286LieBracket (actualRawBlock x) (actualRawBlock y)).1.val 2 2).im)
      (((p286LieBracket (actualRawBlock x) (actualRawBlock y)).1.val 0 0).im)
    simp only [abs_neg] at difference
    nlinarith
  · exact (Complex.abs_re_le_norm _).trans ((weak 0 1).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((weak 0 1).trans (by nlinarith))
  · exact (Complex.abs_im_le_norm _).trans ((weak 0 0).trans (by nlinarith))
  · change |(0 : ℂ).im| ≤ _
    simp only [Complex.zero_im,abs_zero]
    nlinarith

end LowEnergy.PreparationPhaseScalar
