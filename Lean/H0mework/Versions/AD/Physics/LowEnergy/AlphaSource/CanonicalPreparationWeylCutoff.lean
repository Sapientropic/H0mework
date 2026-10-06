import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationBorelPrincipal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationActualFactor
open MeasureTheory Set
open scoped BigOperators ContDiff Topology

def thetaPositionClosed : Set FlatConfiguration :=
  {z | ∀ i, |z i-flatSource i| ≤ sourceRadius}

def thetaDirectionClosed : Set FlatConfiguration :=
  {u | ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius}

def positionRoot (z : FlatConfiguration) : ℝ :=
  ∏ i : Fin 100, factorRoot (2*(z i-flatSource i))

def directionRoot (u : FlatConfiguration) : ℝ :=
  ∏ i : Fin 100, factorRoot (2*(u i-sourceUnitMomentum i))

theorem factorRoot_nonnegative (d : ℝ) : 0 ≤ factorRoot d := by
  rw [factorRoot_literal]
  exact Real.sqrt_nonneg _

theorem factorRoot_le_one (d : ℝ) : factorRoot d ≤ 1 := by
  rw [factorRoot_literal]
  exact Real.sqrt_le_one.mpr (factor_le_one d)

theorem doubled_factorRoot_zero {d : ℝ} (outside : sourceRadius ≤ |d|) :
    factorRoot (2*d)=0 := by
  rw [factorRoot_literal]
  have bound : 2*sourceRadius ≤ |2*d| := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    linarith
  simp only [sourceCutFactor,if_pos bound,Real.sqrt_zero]

theorem positionRoot_nonnegative (z : FlatConfiguration) : 0 ≤ positionRoot z :=
  Finset.prod_nonneg (fun _ _ => factorRoot_nonnegative _)

theorem positionRoot_le_one (z : FlatConfiguration) : positionRoot z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => factorRoot_nonnegative _) (fun _ _ => factorRoot_le_one _)

theorem directionRoot_nonnegative (u : FlatConfiguration) : 0 ≤ directionRoot u :=
  Finset.prod_nonneg (fun _ _ => factorRoot_nonnegative _)

theorem directionRoot_le_one (u : FlatConfiguration) : directionRoot u ≤ 1 :=
  Finset.prod_le_one (fun _ _ => factorRoot_nonnegative _) (fun _ _ => factorRoot_le_one _)

theorem sourceThetaRoot_split (z u : FlatConfiguration) :
    sourceThetaRoot (z,u)=positionRoot z*directionRoot u := rfl

theorem positionRoot_zero_outside {z : FlatConfiguration} (outside : z ∉ thetaPositionClosed) :
    positionRoot z=0 := by
  have fail : ¬ ∀ i, |z i-flatSource i| ≤ sourceRadius := outside
  push Not at fail
  obtain ⟨i,hi⟩ := fail
  exact Finset.prod_eq_zero (Finset.mem_univ i) (doubled_factorRoot_zero hi.le)

theorem directionRoot_zero_outside {u : FlatConfiguration} (outside : u ∉ thetaDirectionClosed) :
    directionRoot u=0 := by
  have fail : ¬ ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius := outside
  push Not at fail
  obtain ⟨i,hi⟩ := fail
  exact Finset.prod_eq_zero (Finset.mem_univ i) (doubled_factorRoot_zero hi.le)

theorem thetaPositionClosed_closed : IsClosed thetaPositionClosed := by
  have same : thetaPositionClosed =
      ⋂ i : Fin 100, {z : FlatConfiguration | |z i-flatSource i| ≤ sourceRadius} := by
    ext z
    simp [thetaPositionClosed]
  rw [same]
  exact isClosed_iInter (fun i => isClosed_le
    ((continuous_apply i).sub continuous_const).abs continuous_const)

theorem thetaDirectionClosed_closed : IsClosed thetaDirectionClosed := by
  have same : thetaDirectionClosed =
      ⋂ i : Fin 100, {u : FlatConfiguration | |u i-sourceUnitMomentum i| ≤ sourceRadius} := by
    ext u
    simp [thetaDirectionClosed]
  rw [same]
  exact isClosed_iInter (fun i => isClosed_le
    ((continuous_apply i).sub continuous_const).abs continuous_const)

theorem thetaPositionClosed_compact : IsCompact thetaPositionClosed := by
  have same : thetaPositionClosed = Set.pi Set.univ (fun i : Fin 100 =>
      Icc (flatSource i-sourceRadius) (flatSource i+sourceRadius)) := by
    ext z
    simp only [thetaPositionClosed,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,forall_true_left,
      Set.mem_Icc]
    apply forall_congr'
    intro i
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [same]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem b1_position_support (p : PhysicalMomentum) :
    tsupport (fun z : FlatConfiguration => b1 (z,p)) ⊆ thetaPositionClosed := by
  apply closure_minimal _ thetaPositionClosed_closed
  intro z hz
  by_contra outside
  apply hz
  simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside outside,
    zero_mul]

theorem b1_position_compact (p : PhysicalMomentum) :
    HasCompactSupport (fun z : FlatConfiguration => b1 (z,p)) :=
  thetaPositionClosed_compact.of_isClosed_subset isClosed_closure (b1_position_support p)

theorem factorWeight_le_one (zp : FlatConfiguration × PhysicalMomentum) : factorWeight zp ≤ 1 := by
  have radial : radialRoot zp.2 ≤ 1 := by
    exact Real.sqrt_le_one.mpr (chi_le_one _)
  have radial_nonnegative : 0 ≤ radialRoot zp.2 := Real.sqrt_nonneg _
  rw [factorWeight,sourceThetaRoot_split]
  exact (mul_le_mul (mul_le_mul (positionRoot_le_one _) (directionRoot_le_one _)
    (directionRoot_nonnegative _) (by norm_num)) radial radial_nonnegative (by norm_num)).trans_eq
      (by norm_num)

theorem factorWeight_nonnegative (zp : FlatConfiguration × PhysicalMomentum) :
    0 ≤ factorWeight zp := by
  rw [factorWeight,sourceThetaRoot_split]
  exact mul_nonneg (mul_nonneg (positionRoot_nonnegative _) (directionRoot_nonnegative _))
    (Real.sqrt_nonneg _)

end LowEnergy.PreparationVacuumWeyl
