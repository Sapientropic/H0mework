import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTimeSourceMatrix

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTimeReader
open PreparationVacuumRationalW
open scoped BigOperators Matrix

def readerCoefficients : Matrix (Fin 13) (Fin 13) ℚ :=
  !![(37375/1728),(-6125/96),(1625/72),(-27125/864),(4375/64),(-875/54),(1625/216),(-875/54),(875/864),(19375/576),(-875/54),(-625/576),(-1625/216);
    (1625/27),(-3500/27),(1625/27),0,0,0,0,0,(-1750/27),(1250/9),(-1750/27),0,0;
    (1625/27),(-3500/27),(1625/27),(-1750/27),(1250/9),(-1750/27),0,0,0,0,0,0,0;
    (1625/27),(-1750/27),0,(-3500/27),(1250/9),0,(1625/27),(-1750/27),0,0,0,0,0;
    (-91/16),(105/8),(-13/2),(-119/8),(15/16),0,(13/2),0,(217/8),(-465/16),14,(15/16),(-13/2);
    (-91/16),(105/8),(-13/2),(217/8),(-465/16),14,(-13/2),0,(-119/8),(15/16),0,(15/16),(13/2);
    (-91/16),(217/8),(-13/2),(105/8),(-465/16),0,(-13/2),14,(-119/8),(15/16),0,(15/16),(13/2);
    0,-28,13,7,15,-7,0,0,7,15,-7,-15,0;
    0,-7,(13/2),-14,15,0,(13/2),-7,7,0,-7,0,0;
    0,-7,(13/2),-7,15,-7,(13/2),-7,0,0,0,0,0;
    (91/4),(-217/4),26,(-7/4),(15/2),(-7/4),(13/8),(-7/4),(-77/4),(105/2),(-105/4),(-15/4),(-13/8);
    (91/4),(-217/4),26,(-91/4),(225/4),(-105/4),0,(-7/4),(7/4),(15/4),(-7/4),(-15/4),0;
    (91/4),(-105/4),(13/8),(-203/4),(225/4),(-7/4),(195/8),(-105/4),(7/4),0,(-7/4),0,0]

def entryCeilings : Matrix (Fin 13) (Fin 13) ℕ :=
  !![15,42,15,21,45,11,5,11,1,23,11,1,5;
    40,86,40,0,0,0,0,0,43,92,43,0,0;
    40,86,40,43,92,43,0,0,0,0,0,0,0;
    40,43,0,86,92,0,40,43,0,0,0,0,0;
    4,9,5,10,1,0,5,0,18,20,10,1,5;
    4,9,5,18,20,10,5,0,10,1,0,1,5;
    4,18,5,9,20,0,5,10,10,1,0,1,5;
    0,19,9,5,10,5,0,0,5,10,5,10,0;
    0,5,5,10,10,0,5,5,5,0,5,0,0;
    0,5,5,5,10,5,5,5,0,0,0,0,0;
    15,36,18,2,5,2,2,2,13,35,18,3,2;
    15,36,18,15,37,18,0,2,2,3,2,3,0;
    15,18,2,34,37,2,17,18,2,0,2,0,0]

def originalRowFactors : Fin 13 → ℕ := ![206,344,344,344,88,88,88,78,50,40,153,151,147]

def inverseScale (i : Fin 13) : ℝ := if i.val<4 then N⁻¹ else N

def generatedReader : Matrix (Fin 13) (Fin 13) ℝ := fun i j => (readerCoefficients i j : ℝ)*N

def sourceReader : Matrix (Fin 13) (Fin 13) ℝ := actualWeights⁻¹

theorem coefficient_normal (i j : Fin 13) :
    readerCoefficients i j=(if i.val<4 then (125/54 : ℚ) else 1)*normalInverse i j := by
  revert i j
  decide +kernel

theorem generated_reader_normal (i j : Fin 13) :
    generatedReader i j=inverseScale i*(normalInverse i j : ℝ) := by
  have factor : (125/54 : ℝ)*N=N⁻¹ := by
    apply (mul_right_cancel₀ N_positive.ne')
    rw [inv_mul_cancel₀ N_positive.ne']
    calc
      (125/54 : ℝ)*N*N=(125/54 : ℝ)*N^2 := by ring
      _ = 1 := by rw [N_square]; norm_num
  unfold generatedReader
  rw [coefficient_normal]
  by_cases small : i.val<4
  · simp only [small,if_true,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,inverseScale]
    calc
      _ = ((125/54 : ℝ)*N)*(normalInverse i j : ℝ) := by ring
      _ = _ := by rw [factor]
  · simp [small,inverseScale,mul_comm]

theorem generated_reader_left : generatedReader*actualWeights=1 := by
  have normal (i k : Fin 13) : (∑ j : Fin 13,(normalInverse i j : ℝ)*(normalWeights j k : ℝ))=
      if i=k then 1 else 0 := by
    have rational := congrArg (fun M : Matrix (Fin 13) (Fin 13) ℚ => M i k) normal_inverse_left
    simp only [Matrix.mul_apply,Matrix.one_apply] at rational
    have cast := congrArg (fun q : ℚ => (q : ℝ)) rational
    push_cast at cast
    by_cases eq : i=k <;> simpa [eq] using cast
  ext i k
  simp only [Matrix.mul_apply,generated_reader_normal,original_weight_normal_form,Matrix.one_apply]
  have group : (∑ j : Fin 13,inverseScale i*(normalInverse i j : ℝ)*((normalWeights j k : ℝ)*weightScale k))=
      inverseScale i*(∑ j : Fin 13,(normalInverse i j : ℝ)*(normalWeights j k : ℝ))*weightScale k := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [group,normal]
  by_cases equal : i=k
  · subst k
    simp only [if_true,mul_one]
    unfold inverseScale weightScale
    split_ifs <;> simp [N_positive.ne']
  · simp [equal]

theorem source_reader_generated : sourceReader=generatedReader := Matrix.inv_eq_left_inv generated_reader_left

theorem source_reader_left : sourceReader*actualWeights=1 := by rw [source_reader_generated]; exact generated_reader_left

private theorem ceiling_from_square (c : ℚ) (k : ℕ) (nonzero : k≠0)
    (lower : (((k-1 : ℕ) : ℚ))^2<c^2*(54/125)) (upper : c^2*(54/125) ≤ (k : ℚ)^2) :
    ⌈|(c : ℝ)*N|⌉₊=k := by
  have square : |(c : ℝ)*N|^2=(c : ℝ)^2*(54/125) := by rw [sq_abs,mul_pow,N_square]
  have lo : (((k-1 : ℕ) : ℝ))^2<(c : ℝ)^2*(54/125) := by
    have cast := (Rat.cast_lt (K:=ℝ)).mpr lower
    push_cast at cast
    exact cast
  have hi : (c : ℝ)^2*(54/125) ≤ (k : ℝ)^2 := by
    have cast := (Rat.cast_le (K:=ℝ)).mpr upper
    push_cast at cast
    exact cast
  rw [Nat.ceil_eq_iff nonzero]
  constructor
  · nlinarith [abs_nonneg ((c : ℝ)*N),(Nat.cast_nonneg (k-1) : (0 : ℝ) ≤ (k-1 : ℕ))]
  · nlinarith [abs_nonneg ((c : ℝ)*N),(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]

theorem ceiling_certificate (i j : Fin 13) :
    (readerCoefficients i j=0 ∧ entryCeilings i j=0) ∨
    (entryCeilings i j≠0 ∧ (((entryCeilings i j-1 : ℕ) : ℚ))^2<(readerCoefficients i j)^2*(54/125) ∧
      (readerCoefficients i j)^2*(54/125) ≤ (entryCeilings i j : ℚ)^2) := by
  revert i j
  decide +kernel

theorem original_entry_ceiling (i j : Fin 13) : ⌈|sourceReader i j|⌉₊=entryCeilings i j := by
  rw [source_reader_generated]
  change ⌈|(readerCoefficients i j : ℝ)*N|⌉₊=_
  rcases ceiling_certificate i j with ⟨zero,kzero⟩|⟨nonzero,lo,hi⟩
  · simp [zero,kzero]
  · exact ceiling_from_square _ _ nonzero lo hi

theorem ceiling_row_sum (i : Fin 13) : (∑ j : Fin 13,entryCeilings i j)=originalRowFactors i := by
  revert i
  decide +kernel

theorem original_row_factors (i : Fin 13) :
    (∑ j : Fin 13,⌈|sourceReader i j|⌉₊)=originalRowFactors i := by
  simp only [original_entry_ceiling,ceiling_row_sum]

theorem reader_row_bound (i : Fin 13) : (∑ j : Fin 13,|sourceReader i j|) ≤ (originalRowFactors i : ℝ) := by
  have estimate := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 13))) => Nat.le_ceil (|sourceReader i j|))
  rw [←Nat.cast_sum,original_row_factors] at estimate
  exact estimate

def sampleValues (v : Fin 13 → ℝ) (t : Fin 13) : ℝ := ∑ j : Fin 13,actualWeights t j*v j

theorem read_original_coefficients (v : Fin 13 → ℝ) (i : Fin 13) :
    (∑ t : Fin 13,sourceReader i t*sampleValues v t)=v i := by
  have inverse (k : Fin 13) : (∑ t : Fin 13,sourceReader i t*actualWeights t k)=if i=k then 1 else 0 :=
    congrArg (fun M : Matrix (Fin 13) (Fin 13) ℝ => M i k) source_reader_left
  unfold sampleValues
  simp only [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,inverse]
  simp

/-- Shared original reader for corrections, classical leaves and first-order families. -/
theorem read_original_functions {X : Type} (F : Fin 13 → X → ℝ) (i : Fin 13) :
    F i=(fun x => ∑ t : Fin 13,sourceReader i t*sampleValues (fun j => F j x) t) := by
  funext x
  exact (read_original_coefficients (fun j => F j x) i).symm

end LowEnergy.PreparationVacuumTimeReader
