import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantPole
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMaterialResponseSuppression

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedSourceAnchor
open SaturationMonoid.PhysicsCore
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentRegularAnchor PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalTailPrice PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalHalfAxis
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open MeasureTheory Filter Set
open scoped BigOperators Topology Interval Matrix
attribute [local irreducible] sourceGreen dressedSignalQuadrature dressedEulerObserver
  sourceLinearBudget sourceConstantBudget factorialBudget

def anchorInput : Fin 4→ℂ := regularPoint

def actualMaterialPoint (event : DressedEvent) (extra : ℝ) (nonnegative : 0 ≤ extra) : DressedEvent :=
  {event with
    energy:=Complex.I*(sourcePairRadius (dressedKinematicPoint event 0) extra:ℂ)
    nonreal:=by
      simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_im,
        Complex.ofReal_re,zero_mul,one_mul,zero_add] using
        (sourcePairRadius_positive (dressedKinematicPoint event 0) extra nonnegative).ne'}

theorem material_kinematics (event : DressedEvent) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    dressedKinematicPoint (actualMaterialPoint event extra nonnegative) 0=
      sourceMaterialPoint (dressedKinematicPoint event 0) extra := rfl

theorem material_observer_unchanged (event : DressedEvent) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    dressedEulerObserver (actualMaterialPoint event extra nonnegative)=dressedEulerObserver event := by
  unfold dressedEulerObserver actualMaterialPoint
  rfl

def materialLinearBudget (event : DressedEvent) : ℝ :=
  2*∑i : Fin 289,sourceLinearBudget (dressedKinematicPoint event 0) (fieldUnit i) 1

def materialConstantBudget (event : DressedEvent) : ℝ :=
  2*∑i : Fin 289,sourceConstantBudget (dressedKinematicPoint event 0) (fieldUnit i) 1

private theorem row_budget_nonnegative (q : PhysicalResponsePoint) (reader : Field289) :
    0 ≤ sourceLinearBudget q reader 1 ∧ 0 ≤ sourceConstantBudget q reader 1 := by
  have left:=factorialBudget_nonnegative q.p q.F 1 (by norm_num)
  have right:=factorialBudget_nonnegative (q.p+q.k) q.F 1 (by norm_num)
  unfold sourceLinearBudget sourceConstantBudget sourceReaderBudget sourceMaterialSlopeBudget
    sourceContactBudget sourceDualCoefficient sourcePrimalCoefficient
  constructor <;> positivity

theorem material_budget_nonnegative (event : DressedEvent) :
    0 ≤ materialLinearBudget event ∧ 0 ≤ materialConstantBudget event := by
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _=>
      (row_budget_nonnegative (dressedKinematicPoint event 0) (fieldUnit i)).1))
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _=>
      (row_budget_nonnegative (dressedKinematicPoint event 0) (fieldUnit i)).2))

/-- Prices are paid at the operator level before the actual two-state observer; no legacy prepared-pair norm enters. -/
theorem material_linear_price (event : DressedEvent) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    dressedSignalLinearCoefficient (actualMaterialPoint event extra nonnegative) 0 1 ≤
      materialLinearBudget event/(sourcePairRadius (dressedKinematicPoint event 0) extra)^2 := by
  unfold dressedSignalLinearCoefficient
  rw [material_kinematics]
  have summed := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>
    sourceHistoryLinearCoefficient_materialPrice (dressedKinematicPoint event 0) extra nonnegative
      (fieldUnit i) 1 (by norm_num))
  have scaled := mul_le_mul_of_nonneg_left summed (by norm_num : (0:ℝ)≤2)
  simpa only [materialLinearBudget,Finset.sum_div,mul_div_assoc] using scaled

theorem material_constant_price (event : DressedEvent) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    dressedSignalConstantCoefficient (actualMaterialPoint event extra nonnegative) 0 1 ≤
      materialConstantBudget event/(sourcePairRadius (dressedKinematicPoint event 0) extra)^2 := by
  unfold dressedSignalConstantCoefficient
  rw [material_kinematics]
  have summed := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>
    sourceHistoryConstantCoefficient_materialPrice (dressedKinematicPoint event 0) extra nonnegative
      (fieldUnit i) 1 (by norm_num))
  have scaled := mul_le_mul_of_nonneg_left summed (by norm_num : (0:ℝ)≤2)
  simpa only [materialConstantBudget,Finset.sum_div,mul_div_assoc] using scaled

def materialWindowBudget (event : DressedEvent) : ℝ :=
  2*(materialLinearBudget event+materialConstantBudget event)*Real.exp 4

def anchorGreenPrice : ℝ := ∑i : Fin 289,∑j : Fin 289,‖sourceGreen generatedRegularPoint i j‖

def anchorExtra (event : DressedEvent) : ℝ :=
  4*(1+anchorGreenPrice*materialWindowBudget event)

private theorem anchorGreenPrice_nonnegative : 0 ≤ anchorGreenPrice :=
  Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))

theorem materialWindowBudget_nonnegative (event : DressedEvent) : 0 ≤ materialWindowBudget event := by
  obtain ⟨hL,hC⟩:=material_budget_nonnegative event
  unfold materialWindowBudget
  positivity

theorem anchorExtra_positive (event : DressedEvent) : 0 < anchorExtra event := by
  have g:=anchorGreenPrice_nonnegative
  have b:=materialWindowBudget_nonnegative event
  unfold anchorExtra
  positivity

/-- Only analytic material labels change; the same actual state, finite frame and physical clock are retained. -/
def anchorEvent (event : DressedEvent) : DressedEvent :=
  actualMaterialPoint event (anchorExtra event) (anchorExtra_positive event).le

def anchorRadius (event : DressedEvent) : ℝ :=
  sourcePairRadius (dressedKinematicPoint event 0) (anchorExtra event)

theorem anchorRadius_positive (event : DressedEvent) : 0 < anchorRadius event :=
  sourcePairRadius_positive _ _ (anchorExtra_positive event).le

private theorem anchor_clock_growth : sourceClockGrowth anchorInput=3 := by
  change max 0 (3:ℝ)=3
  norm_num

/-- The finite-window coincident clock removes exactly its own input exponential; no time normalization is assigned. -/
theorem anchor_window_factor (T : ℝ) : dressedClassicalTimeFactor anchorInput 3 T=(T:ℂ) :=
  dressed_coincident_clock_factor anchorInput T

theorem anchor_weighted_price (event : DressedEvent) (t : ℝ) (future : 0 ≤ t) (small : t≤ 1) :
    ‖dressedSignalWeighted (anchorEvent event) 0 anchorInput 3 t‖ ≤
      materialWindowBudget event/(anchorRadius event)^2 := by
  have linear:=material_linear_price event (anchorExtra event) (anchorExtra_positive event).le
  have constant:=material_constant_price event (anchorExtra event) (anchorExtra_positive event).le
  have budgets:=material_budget_nonnegative event
  have radius:=anchorRadius_positive event
  have source:=dressed_signal_quadrature_price (anchorEvent event) 0 anchorInput 1 t (by norm_num) future
  rw [anchor_clock_growth] at source
  have scaled : ‖dressedSignalWeighted (anchorEvent event) 0 anchorInput 3 t‖ ≤
      Real.exp (-3*t)*(2*(dressedSignalLinearCoefficient (anchorEvent event) 0 1*t+
        dressedSignalConstantCoefficient (anchorEvent event) 0 1)*Real.exp ((4*1+3)*t)) := by
    have normed := norm_smul (laplaceWeight (3:ℂ) t) (dressedSignalQuadrature (anchorEvent event) 0 anchorInput t)
    rw [laplace_norm] at normed
    exact le_trans (le_of_eq normed) (mul_le_mul_of_nonneg_left source (Real.exp_pos _).le)
  have polynomial : dressedSignalLinearCoefficient (anchorEvent event) 0 1*t+
      dressedSignalConstantCoefficient (anchorEvent event) 0 1 ≤
        (materialLinearBudget event+materialConstantBudget event)/(anchorRadius event)^2 := by
    have first := (mul_le_mul_of_nonneg_right linear future).trans
      (mul_le_of_le_one_right (div_nonneg budgets.1 (sq_nonneg _)) small)
    exact (add_le_add first constant).trans_eq (by unfold anchorRadius;ring)
  have price := scaled.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left polynomial (by norm_num : (0:ℝ)≤2))
      (Real.exp_pos _).le) (Real.exp_pos _).le)
  have exponential : Real.exp (4*t)≤Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
  have identity (b : ℝ) : Real.exp (-3*t)*(2*b*Real.exp ((4*1+3)*t))=2*b*Real.exp (4*t) := by
    calc
      _=2*b*(Real.exp (-3*t)*Real.exp ((4*1+3)*t)) := by ring
      _=_ := by
        rw [←Real.exp_add]
        congr 2
        ring
  rw [identity] at price
  have nonnegative : 0 ≤ 2*((materialLinearBudget event+materialConstantBudget event)/(anchorRadius event)^2) :=
    mul_nonneg (by norm_num) (div_nonneg (add_nonneg budgets.1 budgets.2) (sq_nonneg _))
  exact price.trans ((mul_le_mul_of_nonneg_left exponential nonnegative).trans_eq (by
    unfold materialWindowBudget
    ring))

/-- The original nonlinear source supplies a positive observation window for the same actual amplitude. -/
def anchorWindow (event : DressedEvent) (a : SignalAmplitude) : ℝ :=
  min 1 (dressedSignalDuration (anchorEvent event) 0 anchorInput a/2)

theorem anchor_window_source (event : DressedEvent) (a : SignalAmplitude) :
    0 < anchorWindow event a ∧ anchorWindow event a ≤ 1 ∧
      anchorWindow event a < dressedSignalDuration (anchorEvent event) 0 anchorInput a := by
  have positive:=dressed_signal_duration_positive (anchorEvent event) 0 anchorInput a
  refine ⟨lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  exact (min_le_right _ _).trans_lt (by linarith)

/-- The contraction coefficient is generated from actual source operator bounds, without an inverse premise. -/
theorem anchor_feedback_coefficient (event : DressedEvent) :
    anchorGreenPrice*materialWindowBudget event/(anchorRadius event)^2 ≤ (1/16:ℝ) := by
  have g:=anchorGreenPrice_nonnegative
  have b:=materialWindowBudget_nonnegative event
  have r:=anchorRadius_positive event
  have radius : 4*(1+anchorGreenPrice*materialWindowBudget event) ≤ anchorRadius event := by
    unfold anchorRadius sourcePairRadius anchorExtra
    have left:=norm_nonneg (sourceBaseGenerator
      ((dressedKinematicPoint event 0).p+(dressedKinematicPoint event 0).k) (dressedKinematicPoint event 0).F)
    have right:=norm_nonneg (sourceBaseGenerator (dressedKinematicPoint event 0).p (dressedKinematicPoint event 0).F)
    nlinarith [mul_nonneg g b]
  apply (div_le_iff₀ (sq_pos_of_pos r)).mpr
  have square:=mul_self_le_mul_self (by positivity : 0 ≤ 4*(1+anchorGreenPrice*materialWindowBudget event)) radius
  nlinarith [sq_nonneg (anchorGreenPrice*materialWindowBudget event)]

end LowEnergy.GaussComposite.ActualEMDressedSourceAnchor
