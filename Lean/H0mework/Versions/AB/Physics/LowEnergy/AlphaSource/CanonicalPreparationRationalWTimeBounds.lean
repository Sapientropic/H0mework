import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalArrays
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityOriginalArrays
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalTimePairTensor

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRationalW
open GaussNativeEnergy SourceQuantumConfigurationHilbert
open PreparationVacuumLowerLeaves PreparationVacuumCoframeBudget
open scoped BigOperators ContDiff Topology

def N : ℝ := sourceTime 0
def delta (n : ℝ) (b : Fin 3 → ℝ) : ℝ := n^2-∑ i,b i^2
structure TimeBox (n : ℝ) (b : Fin 3 → ℝ) : Prop where
  lower : N ≤ n
  upper : n ≤ 2*N
  shift : ∀ i,|b i| ≤ N/4

theorem N_positive : 0<N := by
  rw [N,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

theorem N_square : N^2=54/125 := by
  rw [N,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_sq

theorem N_bounds : (13/20 : ℝ)<N ∧ N<2/3 := by
  constructor <;> nlinarith [N_positive,N_square]

theorem delta_floor (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    13*N^2/16 ≤ delta n b := by
  have square (i : Fin 3) : b i^2 ≤ N^2/16 := by
    have bound := abs_le.mp (time.shift i)
    nlinarith [sq_nonneg (b i-N/4),sq_nonneg (b i+N/4)]
  unfold delta
  rw [Fin.sum_univ_three]
  nlinarith [time.lower,N_positive,square 0,square 1,square 2]

theorem time_positive (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    0<n ∧ 0<delta n b := by
  have np := N_positive
  exact ⟨N_positive.trans_le time.lower,lt_of_lt_of_le (by positivity) (delta_floor n b time)⟩

def timeInverse : ℝ := 16/(13*N^3)

theorem timeInverse_bounds : 4<timeInverse ∧ timeInverse<5 := by
  have np := N_positive
  have den : 0<13*N^3 := by positivity
  have cube : N^3=(54/125 : ℝ)*N := by rw [pow_succ,N_square]
  constructor
  · rw [timeInverse,lt_div_iff₀ den,cube]
    nlinarith [N_bounds.2]
  · rw [timeInverse,div_lt_iff₀ den,cube]
    nlinarith [N_bounds.1]

theorem actual_time_inverse (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    |(n*delta n b)⁻¹| ≤ timeInverse := by
  have np := N_positive
  obtain ⟨hn,hd⟩ := time_positive n b time
  have floor : 13*N^3/16 ≤ n*delta n b := by
    have estimate := mul_le_mul time.lower (delta_floor n b time) (by positivity : (0 : ℝ) ≤ 13*N^2/16) hn.le
    calc
      13*N^3/16 = N*(13*N^2/16) := by ring
      _ ≤ _ := estimate
  rw [abs_of_pos (inv_pos.mpr (mul_pos hn hd))]
  have estimate := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<13*N^3/16) floor
  calc
    (n*delta n b)⁻¹ = 1/(n*delta n b) := by rw [one_div]
    _ ≤ 1/(13*N^3/16) := estimate
    _ = timeInverse := by unfold timeInverse; field_simp

def CoefficientSupported (c : ℚ) : Prop := |c|=1/2 ∨ |c|=1
instance : DecidablePred CoefficientSupported := fun _ => by unfold CoefficientSupported; infer_instance

def coefficientCeiling (c : ℚ) : ℕ := if |c|=1/2 then 3 else 5

theorem original_absolute_ceiling (c : ℚ) (supported : CoefficientSupported c) :
    ⌈|(c : ℝ)| *timeInverse⌉₊=coefficientCeiling c := by
  rcases supported with half|one
  · have real : |(c : ℝ)|=1/2 := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) half
      norm_num at h
      exact h
    rw [real,coefficientCeiling,if_pos half,Nat.ceil_eq_iff (by decide)]
    norm_num
    constructor <;> linarith [timeInverse_bounds.1,timeInverse_bounds.2]
  · have real : |(c : ℝ)|=1 := by exact_mod_cast one
    have ne : ¬ |c|=1/2 := by rw [one]; norm_num
    rw [real,one_mul,coefficientCeiling,if_neg ne,Nat.ceil_eq_iff (by decide)]
    norm_num
    exact ⟨timeInverse_bounds.1,timeInverse_bounds.2.le⟩

theorem actual_time_coefficient (c : ℚ) (supported : CoefficientSupported c)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    |(c : ℝ)/(n*delta n b)| ≤ (coefficientCeiling c : ℝ) := by
  calc
    _ = |(c : ℝ)| *|(n*delta n b)⁻¹| := by rw [div_eq_mul_inv,abs_mul]
    _ ≤ |(c : ℝ)| *timeInverse := mul_le_mul_of_nonneg_left (actual_time_inverse n b time) (abs_nonneg _)
    _ ≤ _ := by rw [←original_absolute_ceiling c supported]; exact Nat.le_ceil _

abbrev TimePowers := Fin 4 → ℕ
abbrev TimeTerms := List (ℚ × TimePowers)
def timeCoordinate (n : ℝ) (b : Fin 3 → ℝ) : Fin 4 → ℝ := ![n,b 0,b 1,b 2]
def timeMonomial (a : TimePowers) (n : ℝ) (b : Fin 3 → ℝ) : ℝ := ∏ i,timeCoordinate n b i^a i

theorem time_coordinate_bound (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (i : Fin 4) :
    |timeCoordinate n b i| ≤ if i=0 then 2 else 1 := by
  have nn := (time_positive n b time).1
  have nb := N_bounds.2
  fin_cases i
  · norm_num [timeCoordinate,abs_of_pos nn]
    linarith [time.upper]
  · norm_num [timeCoordinate]
    linarith [time.shift 0]
  · norm_num [timeCoordinate]
    linarith [time.shift 1]
  · norm_num [timeCoordinate]
    linarith [time.shift 2]

theorem time_monomial_bound (a : TimePowers) (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    |timeMonomial a n b| ≤ 2^(a 0) := by
  unfold timeMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  calc
    _ ≤ ∏ i : Fin 4,if i=0 then (2 : ℝ)^a i else 1 := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _
        have estimate := pow_le_pow_left₀ (abs_nonneg (timeCoordinate n b i)) (time_coordinate_bound n b time i) (a i)
        split_ifs with h
        · simpa only [h,if_true] using estimate
        · simpa only [h,if_false,one_pow] using estimate
    _ = _ := by simp

def timeValue (ts : TimeTerms) (n : ℝ) (b : Fin 3 → ℝ) : ℝ :=
  (ts.map (fun t => ((t.1 : ℝ)/(n*delta n b))*timeMonomial t.2 n b)).sum

def timeAmplitude (ts : TimeTerms) : ℕ := (ts.map (fun t => coefficientCeiling t.1*2^(t.2 0))).sum

theorem timeValue_budget (ts : TimeTerms) (supported : ∀ t∈ts,CoefficientSupported t.1)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) :
    |timeValue ts n b| ≤ (timeAmplitude ts : ℝ) := by
  induction ts with
  | nil => simp [timeValue,timeAmplitude]
  | cons t ts ih =>
    have bound := mul_le_mul (actual_time_coefficient t.1 (supported t (by simp)) n b time)
      (time_monomial_bound t.2 n b time) (abs_nonneg _) (Nat.cast_nonneg _)
    change |((t.1 : ℝ)/(n*delta n b))*timeMonomial t.2 n b+timeValue ts n b| ≤ _
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using bound)
      (ih (fun t ht => supported t (by simp [ht])))).trans_eq ?_)
    simp [timeAmplitude,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]

end LowEnergy.PreparationVacuumRationalW
