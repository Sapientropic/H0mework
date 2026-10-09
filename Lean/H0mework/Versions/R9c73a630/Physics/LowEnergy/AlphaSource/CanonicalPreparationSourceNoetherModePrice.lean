import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNoetherContactBudget

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherResponsePrice
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMatterEulerFeedback PreparationVacuumPhysicalTailPrice
open PreparationVacuumIndependentMomentumReturn
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumOrderedRealSignal
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open scoped Topology BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] physicalTime jointResolvent rawReader rawReaderContact noetherReaderContact
  fiveDerivative fiveCoefficient rawCoefficient

def noetherFiveCoefficient (q : PhysicalResponsePoint) (reader force : Field289) (eta : ℝ) : ℝ:=
  fiveCoefficient q reader force eta+correctedContactCoefficient q reader force eta

theorem noetherFiveCoefficient_nonnegative (q : PhysicalResponsePoint) (reader force : Field289)
    (eta : ℝ) (positive : 0<eta) : 0 ≤ noetherFiveCoefficient q reader force eta :=
  add_nonneg (fiveCoefficient_nonnegative q reader force eta positive)
    (correctedContactCoefficient_nonnegative q reader force eta positive)

def noetherSlopeKernel (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) : SourceOperator:=
  fiveDerivative reader force q.p q.k q.F q.z q.w t+(correctedContactJet q reader force t).value

theorem noetherSlopeKernel_price (q : PhysicalResponsePoint) (reader force : Field289) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖noetherSlopeKernel q reader force t‖≤noetherFiveCoefficient q reader force eta*Real.exp (4*eta*t) :=by
  have extra:=correctedContactKernel_price q reader force eta t positive future
  have expBound : Real.exp (2*eta*t)≤Real.exp (4*eta*t):=
    Real.exp_le_exp.mpr (by nlinarith)
  have corrected:=extra.trans (mul_le_mul_of_nonneg_left expBound
    (correctedContactCoefficient_nonnegative q reader force eta positive))
  exact (norm_add_le _ _).trans ((add_le_add (fiveKernel_price q reader force eta t positive future) corrected).trans_eq
    (by rw [noetherFiveCoefficient,add_mul]))

private theorem paired_kernel_price (x y : H) (A : SourceOperator) (C : ℝ) (source : ‖A‖≤C) :
    ‖inner ℂ x (A y)‖≤‖x‖*‖y‖*C :=by
  refine (norm_inner_le_norm x (A y)).trans ?_
  refine (mul_le_mul_of_nonneg_left ((A.le_opNorm y).trans
    (mul_le_mul_of_nonneg_right source (norm_nonneg y))) (norm_nonneg x)).trans_eq ?_
  ring

def noetherScalarCoefficient (q : PhysicalResponsePoint) (reader force : Field289)
    (response : Bool) (eta : ℝ) : ℝ:=
  ‖responseLeft q‖*‖responseRight q‖*
    (if response then noetherFiveCoefficient q reader force eta else rawCoefficient q reader eta)

theorem noetherScalarCoefficient_nonnegative (q : PhysicalResponsePoint) (reader force : Field289)
    (response : Bool) (eta : ℝ) (positive : 0<eta) : 0 ≤ noetherScalarCoefficient q reader force response eta :=by
  cases response
  · have price:=rawCoefficient_nonnegative q reader eta positive
    unfold noetherScalarCoefficient
    simp only [Bool.false_eq_true,↓reduceIte]
    positivity
  · have price:=noetherFiveCoefficient_nonnegative q reader force eta positive
    unfold noetherScalarCoefficient
    simp only [↓reduceIte]
    positivity

theorem noetherScalarSignal_price (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool)
    (eta t : ℝ) (positive : 0<eta) (future : 0≤t) :
    ‖(branchTimeJet q reader force response t).value‖≤
      noetherScalarCoefficient q reader force response eta*Real.exp (4*eta*t) :=by
  cases response
  · have price:=paired_kernel_price (responseLeft q) (responseRight q) _ _
      (rawKernel_price q reader eta t positive future)
    simpa only [branchTimeJet,Bool.false_eq_true,↓reduceIte,preparedTimeJet,pairJet,rawKernelJet_value,
      noetherScalarCoefficient,mul_assoc] using price
  · have price:=paired_kernel_price (responseLeft q) (responseRight q) _ _
      (noetherSlopeKernel_price q reader force eta t positive future)
    simpa only [branchTimeJet,↓reduceIte,preparedSlopeTimeJet,pairJet,addJet,slopeKernelJet_value,
      noetherScalarCoefficient,noetherSlopeKernel,mul_assoc] using price

def noetherModeCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta : ℝ) (wave : PhysicalMomentum) (i : Fin 289) : ℝ:=
  let F:=noetherScalarCoefficient q (fieldUnit i) force response eta
  let R:=noetherScalarCoefficient (oppositeCoordinates q) (fieldUnit i) force response eta
  let DR:=noetherScalarCoefficient (crossRightCoordinates q) (fieldUnit i) force response eta
  let DL:=noetherScalarCoefficient (crossLeftCoordinates q) (fieldUnit i) force response eta
  (if -q.k=wave then (1/2:ℝ)*(F+R) else 0)+(if q.k=wave then (1/2:ℝ)*(R+F) else 0)+
    (if 2 • q.p+q.k=wave then (1/2:ℝ)*(DR+DL) else 0)+
      (if -(2 • q.p+q.k)=wave then (1/2:ℝ)*(DL+DR) else 0)

theorem noetherModeCoefficient_nonnegative (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta : ℝ) (positive : 0<eta) (wave : PhysicalMomentum) (i : Fin 289) :
    0 ≤ noetherModeCoefficient q force response eta wave i :=by
  have F:=noetherScalarCoefficient_nonnegative q (fieldUnit i) force response eta positive
  have R:=noetherScalarCoefficient_nonnegative (oppositeCoordinates q) (fieldUnit i) force response eta positive
  have DR:=noetherScalarCoefficient_nonnegative (crossRightCoordinates q) (fieldUnit i) force response eta positive
  have DL:=noetherScalarCoefficient_nonnegative (crossLeftCoordinates q) (fieldUnit i) force response eta positive
  dsimp only [noetherModeCoefficient]
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · split
        · exact mul_nonneg (by norm_num) (add_nonneg F R)
        · exact le_rfl
      · split
        · exact mul_nonneg (by norm_num) (add_nonneg R F)
        · exact le_rfl
    · split
      · exact mul_nonneg (by norm_num) (add_nonneg DR DL)
      · exact le_rfl
  · split
    · exact mul_nonneg (by norm_num) (add_nonneg DL DR)
    · exact le_rfl

private theorem source_half_price (a b : ℂ) (A B E : ℝ) (ha : ‖a‖≤A*E) (hb : ‖b‖≤B*E) :
    ‖(1/2:ℂ)*(a+star b)‖≤(1/2:ℝ)*(A+B)*E :=by
  rw [norm_mul,show ‖(1/2:ℂ)‖=(1/2:ℝ) from by norm_num]
  have sum : ‖a+star b‖≤A*E+B*E:=by
    refine (norm_add_le _ _).trans ?_
    rw [norm_star]
    exact add_le_add ha hb
  refine (mul_le_mul_of_nonneg_left sum (show (0:ℝ)≤1/2 from by norm_num)).trans_eq ?_
  ring

private theorem source_single_price (a : ℂ) (C E : ℝ) (source : ‖a‖≤C*E) (key wave : PhysicalMomentum) :
    ‖Finsupp.single key a wave‖≤(if key=wave then C else 0)*E :=by
  by_cases same : key=wave
  · simpa only [Finsupp.single_apply,if_pos same] using source
  · simp only [Finsupp.single_apply,if_neg same,norm_zero,zero_mul,le_refl]

theorem noetherRealMode_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta t : ℝ) (positive : 0<eta) (future : 0≤t) (wave : PhysicalMomentum) (i : Fin 289) :
    ‖(realEulerTimeJet q force response t wave i).value‖≤
      noetherModeCoefficient q force response eta wave i*Real.exp (4*eta*t) :=by
  have F:=noetherScalarSignal_price q (fieldUnit i) force response eta t positive future
  have R:=noetherScalarSignal_price (oppositeCoordinates q) (fieldUnit i) force response eta t positive future
  have DR:=noetherScalarSignal_price (crossRightCoordinates q) (fieldUnit i) force response eta t positive future
  have DL:=noetherScalarSignal_price (crossLeftCoordinates q) (fieldUnit i) force response eta t positive future
  let f:=(branchTimeJet q (fieldUnit i) force response t).value
  let r:=(branchTimeJet (oppositeCoordinates q) (fieldUnit i) force response t).value
  let cr:=(branchTimeJet (crossRightCoordinates q) (fieldUnit i) force response t).value
  let cl:=(branchTimeJet (crossLeftCoordinates q) (fieldUnit i) force response t).value
  have a:=source_single_price _ _ _ (source_half_price f r _ _ _ F R) (-q.k) wave
  have b:=source_single_price _ _ _ (source_half_price r f _ _ _ R F) q.k wave
  have c:=source_single_price _ _ _ (source_half_price cr cl _ _ _ DR DL) (2 • q.p+q.k) wave
  have d:=source_single_price _ _ _ (source_half_price cl cr _ _ _ DL DR) (-(2 • q.p+q.k)) wave
  have shape : (realEulerTimeJet q force response t wave i).value=
      -(Finsupp.single (-q.k) ((1/2:ℂ)*(f+star r)) wave+
        Finsupp.single q.k ((1/2:ℂ)*(r+star f)) wave+
          Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(cr+star cl)) wave+
            Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(cl+star cr)) wave):=by
    rw [realEulerTimeJet_value]
    cases response <;>
      simp only [Bool.false_eq_true,↓reduceIte,realEulerCoefficients,realEulerSlope,realDensityCoefficients,
        coefficientSlope,f,r,cr,cl,branchTimeJet,preparedTimeJet_value,preparedSlopeTimeJet_value,
        Finsupp.add_apply,oppositeCurrent_actual,crossRight_actual,crossLeft_actual]
  rw [shape,norm_neg]
  refine ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add a b)) c)) d)).trans_eq ?_
  simp only [noetherModeCoefficient,add_mul]

end LowEnergy.PreparationVacuumNoetherResponsePrice
