import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalOperator

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumPropagationPencil
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumPhysicalFeedback PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumGaugeSourceInjection
open ActualDressedFullCoulomb ActualDressedNoether
open SourceFiniteUnitary PreparationVacuumPhysicalTailPrice
open scoped BigOperators Topology
attribute [local irreducible] dressedEulerObserver sourceHistoryOperator rawInitial factorialBudget jointCurrent

private theorem history_coefficient_nonnegative (q : PhysicalResponsePoint) (reader : Field289)
    (eta : ℝ) (positive : 0<eta) :
    0  ≤  sourceHistoryLinearCoefficient q reader eta  ∧
      0  ≤  sourceHistoryConstantCoefficient q reader eta := by
  have left:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have right:=factorialBudget_nonnegative q.p q.F eta positive
  constructor
  · unfold sourceHistoryLinearCoefficient sourceDualCoefficient sourcePrimalCoefficient
    positivity
  · unfold sourceHistoryConstantCoefficient sourceMiddleCoefficient
    positivity

def dressedSignalLinearCoefficient (event : DressedEvent) (transfer : PhysicalMomentum) (eta : ℝ) : ℝ :=
  2*∑i : Fin 289,sourceHistoryLinearCoefficient (dressedKinematicPoint event transfer) (fieldUnit i) eta

def dressedSignalConstantCoefficient (event : DressedEvent) (transfer : PhysicalMomentum) (eta : ℝ) : ℝ :=
  2*∑i : Fin 289,sourceHistoryConstantCoefficient (dressedKinematicPoint event transfer) (fieldUnit i) eta

theorem dressed_signal_coefficient_nonnegative (event : DressedEvent) (transfer : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) :
    0 ≤ dressedSignalLinearCoefficient event transfer eta  ∧
      0 ≤ dressedSignalConstantCoefficient event transfer eta := by
  constructor
  · unfold dressedSignalLinearCoefficient
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact (history_coefficient_nonnegative _ _ eta positive).1
  · unfold dressedSignalConstantCoefficient
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact (history_coefficient_nonnegative _ _ eta positive).2

private theorem observed_signal_price (q : PhysicalResponsePoint) (observer : SourceOp→L[ℝ]ℂ)
    (observed : ‖observer‖ ≤ 2) (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖ContinuousLinearMap.pi (fun i : Fin 289=>observer.comp (sourceHistoryOperator q (fieldUnit i) p t))‖ ≤
      ((2*∑i : Fin 289,sourceHistoryLinearCoefficient q (fieldUnit i) eta)*t+
        (2*∑i : Fin 289,sourceHistoryConstantCoefficient q (fieldUnit i) eta))*
          Real.exp ((4*eta+sourceClockGrowth p)*t) := by
  have eachNonnegative (i : Fin 289) :
      0 ≤ sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+
        sourceHistoryConstantCoefficient q (fieldUnit i) eta := by
    have coefficients:=history_coefficient_nonnegative q (fieldUnit i) eta positive
    exact add_nonneg (mul_nonneg coefficients.1 future) coefficients.2
  apply ContinuousLinearMap.norm_pi_le_of_le
  · intro i
    have price:=sourceHistoryOperator_price q (fieldUnit i) p eta t positive future
    have individual : ‖observer.comp (sourceHistoryOperator q (fieldUnit i) p t)‖ ≤
        ‖observer‖*((sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+
          sourceHistoryConstantCoefficient q (fieldUnit i) eta)*Real.exp ((4*eta+sourceClockGrowth p)*t)) :=
      (ContinuousLinearMap.opNorm_comp_le observer (sourceHistoryOperator q (fieldUnit i) p t)).trans
        (mul_le_mul_of_nonneg_left price (norm_nonneg observer))
    have bound : 0 ≤ (sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+
        sourceHistoryConstantCoefficient q (fieldUnit i) eta)*Real.exp ((4*eta+sourceClockGrowth p)*t) :=
      mul_nonneg (eachNonnegative i) (Real.exp_pos _).le
    have actual:=individual.trans (mul_le_mul_of_nonneg_right observed bound)
    have single : sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+
        sourceHistoryConstantCoefficient q (fieldUnit i) eta ≤
        ∑j : Fin 289,(sourceHistoryLinearCoefficient q (fieldUnit j) eta*t+
          sourceHistoryConstantCoefficient q (fieldUnit j) eta) :=
      Finset.single_le_sum (fun j _=>eachNonnegative j) (Finset.mem_univ i)
    refine actual.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right single (Real.exp_pos _).le) (by norm_num : (0:ℝ) ≤ 2)).trans_eq ?_)
    simp only [Finset.sum_add_distrib,←Finset.sum_mul]
    ring
  · apply mul_nonneg _ (Real.exp_pos _).le
    apply add_nonneg
    · apply mul_nonneg _ future
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun i _=>(history_coefficient_nonnegative q (fieldUnit i) eta positive).1)
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun i _=>(history_coefficient_nonnegative q (fieldUnit i) eta positive).2)

/-- Source operator prices are paid before observing either actual state. -/
theorem dressed_signal_operator_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖dressedSignalOperator event transfer p t‖ ≤
      (dressedSignalLinearCoefficient event transfer eta*t+
        dressedSignalConstantCoefficient event transfer eta)*Real.exp ((4*eta+sourceClockGrowth p)*t) := by
  have observed : ‖(dressedEulerObserver event).restrictScalars ℝ‖ ≤ 2 := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact dressed_euler_observer_price event
  exact observed_signal_price (dressedKinematicPoint event transfer)
    ((dressedEulerObserver event).restrictScalars ℝ) observed p eta t positive future

private theorem scalar_operator_price {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G] (c : ℂ) (A : E→L[ℝ]G) : ‖c • A‖ ≤ ‖c‖*‖A‖ := by
  apply (c • A).opNorm_le_bound (mul_nonneg (norm_nonneg c) A.opNorm_nonneg)
  intro x
  rw [smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg c)

private theorem quadrature_price : ‖sourceQuadratureOperator‖ ≤ 1 := by
  have price:=scalar_operator_price (-Complex.I) (ContinuousLinearMap.id ℝ SignalAmplitude)
  simpa only [sourceQuadratureOperator,norm_neg,Complex.norm_I,one_mul] using
    price.trans (by simpa only [norm_neg,Complex.norm_I,one_mul] using
      ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=SignalAmplitude))

theorem dressed_signal_quadrature_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0 ≤ t) :
    ‖dressedSignalQuadrature event transfer p t‖  ≤
      2*(dressedSignalLinearCoefficient event transfer eta*t+
        dressedSignalConstantCoefficient event transfer eta)*Real.exp ((4*eta+sourceClockGrowth p)*t) := by
  have rotation : ‖(dressedSignalOperator event transfer p t).comp sourceQuadratureOperator‖  ≤
      ‖dressedSignalOperator event transfer p t‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left quadrature_price (norm_nonneg _)).trans_eq (mul_one _))
  have imaginary:=scalar_operator_price Complex.I
    ((dressedSignalOperator event transfer p t).comp sourceQuadratureOperator)
  simp only [Complex.norm_I,one_mul] at imaginary
  have current:=dressed_signal_operator_price event transfer p eta t positive future
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans
    ((add_le_add current (imaginary.trans (rotation.trans current))).trans_eq (by ring))

end LowEnergy.GaussComposite.ActualDressedSignal
