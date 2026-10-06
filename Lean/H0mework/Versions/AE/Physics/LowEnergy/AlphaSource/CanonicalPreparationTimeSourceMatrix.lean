import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerActualConsumers

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTimeReader
open PreparationVacuumRationalW PreparationVacuumEnergyTail GaussNativeEnergy
open scoped BigOperators ContDiff Topology Matrix

def pointSigns : Matrix (Fin 13) (Fin 3) ℝ :=
  !![-1,-1,-1;-1,-1,0;-1,-1,1;-1,0,-1;-1,0,0;-1,0,1;-1,1,-1;-1,1,0;
    0,-1,-1;0,-1,0;0,-1,1;0,0,-1;1,-1,-1]

def pointShift (t : Fin 13) (i : Fin 3) : ℝ := (N/4)*pointSigns t i

def actualWeights : Matrix (Fin 13) (Fin 13) ℝ := fun t j => originalTemporalWeights N (pointShift t) j

def weightScale (j : Fin 13) : ℝ := if j.val<4 then N else N⁻¹

theorem original_N_expression : N=3*Real.sqrt 30/25 := by
  apply (sq_eq_sq₀ N_positive.le (by positivity : (0 : ℝ) ≤ 3*Real.sqrt 30/25)).mp
  rw [N_square]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

theorem pointSigns_bound (t : Fin 13) (i : Fin 3) : |pointSigns t i| ≤ 1 := by
  fin_cases t <;> fin_cases i <;> norm_num [pointSigns]

theorem actual_point_box (t : Fin 13) : TimeBox N (pointShift t) := by
  have np := N_positive
  constructor
  · rfl
  · linarith [N_positive]
  · intro i
    rw [pointShift,abs_mul,abs_of_pos (div_pos N_positive (by norm_num))]
    exact (mul_le_mul_of_nonneg_left (pointSigns_bound t i) (by positivity)).trans_eq (mul_one _)

def normalWeights : Matrix (Fin 13) (Fin 13) ℚ :=
  !![1,(-1/4),(-1/4),(-1/4),(15/26),(15/26),(15/26),(-1/13),(-1/13),(-1/13),(4/13),(4/13),(4/13);
    1,(-1/4),(-1/4),0,(15/28),(15/28),(4/7),(-1/14),0,0,(2/7),(2/7),0;
    1,(-1/4),(-1/4),(1/4),(15/26),(15/26),(15/26),(-1/13),(1/13),(1/13),(4/13),(4/13),(-4/13);
    1,(-1/4),0,(-1/4),(15/28),(4/7),(15/28),0,(-1/14),0,(2/7),0,(2/7);
    1,(-1/4),0,0,(1/2),(8/15),(8/15),0,0,0,(4/15),0,0;
    1,(-1/4),0,(1/4),(15/28),(4/7),(15/28),0,(1/14),0,(2/7),0,(-2/7);
    1,(-1/4),(1/4),(-1/4),(15/26),(15/26),(15/26),(1/13),(-1/13),(1/13),(4/13),(-4/13),(4/13);
    1,(-1/4),(1/4),0,(15/28),(15/28),(4/7),(1/14),0,0,(2/7),(-2/7),0;
    1,0,(-1/4),(-1/4),(4/7),(15/28),(15/28),0,0,(-1/14),0,(2/7),(2/7);
    1,0,(-1/4),0,(8/15),(1/2),(8/15),0,0,0,0,(4/15),0;
    1,0,(-1/4),(1/4),(4/7),(15/28),(15/28),0,0,(1/14),0,(2/7),(-2/7);
    1,0,0,(-1/4),(8/15),(8/15),(1/2),0,0,0,0,0,(4/15);
    1,(1/4),(-1/4),(-1/4),(15/26),(15/26),(15/26),(1/13),(1/13),(-1/13),(-4/13),(4/13),(4/13)]

def normalInverse : Matrix (Fin 13) (Fin 13) ℚ :=
  !![(299/32),(-441/16),(39/4),(-217/16),(945/32),-7,(13/4),-7,(7/16),(465/32),-7,(-15/32),(-13/4);
    26,-56,26,0,0,0,0,0,-28,60,-28,0,0;
    26,-56,26,-28,60,-28,0,0,0,0,0,0,0;
    26,-28,0,-56,60,0,26,-28,0,0,0,0,0;
    (-91/16),(105/8),(-13/2),(-119/8),(15/16),0,(13/2),0,(217/8),(-465/16),14,(15/16),(-13/2);
    (-91/16),(105/8),(-13/2),(217/8),(-465/16),14,(-13/2),0,(-119/8),(15/16),0,(15/16),(13/2);
    (-91/16),(217/8),(-13/2),(105/8),(-465/16),0,(-13/2),14,(-119/8),(15/16),0,(15/16),(13/2);
    0,-28,13,7,15,-7,0,0,7,15,-7,-15,0;
    0,-7,(13/2),-14,15,0,(13/2),-7,7,0,-7,0,0;
    0,-7,(13/2),-7,15,-7,(13/2),-7,0,0,0,0,0;
    (91/4),(-217/4),26,(-7/4),(15/2),(-7/4),(13/8),(-7/4),(-77/4),(105/2),(-105/4),(-15/4),(-13/8);
    (91/4),(-217/4),26,(-91/4),(225/4),(-105/4),0,(-7/4),(7/4),(15/4),(-7/4),(-15/4),0;
    (91/4),(-105/4),(13/8),(-203/4),(225/4),(-7/4),(195/8),(-105/4),(7/4),0,(-7/4),0,0]

theorem original_weight_normal_form (t j : Fin 13) :
    actualWeights t j=(normalWeights t j : ℝ)*weightScale j := by
  have nn := N_positive.ne'
  fin_cases t <;> fin_cases j <;>
    norm_num [actualWeights,originalTemporalWeights,pointShift,pointSigns,normalWeights,weightScale,Fin.sum_univ_three]
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring_nf
  all_goals first | field_simp [nn] | simp
  all_goals simp

theorem normal_inverse_left : normalInverse*normalWeights=1 := by
  ext i j
  have finite : ∀ i j : Fin 13,(normalInverse*normalWeights) i j=(1 : Matrix (Fin 13) (Fin 13) ℚ) i j := by
    decide +kernel
  exact finite i j

theorem normal_inverse_right : normalWeights*normalInverse=1 := by
  ext i j
  have finite : ∀ i j : Fin 13,(normalWeights*normalInverse) i j=(1 : Matrix (Fin 13) (Fin 13) ℚ) i j := by
    decide +kernel
  exact finite i j

end LowEnergy.PreparationVacuumTimeReader
