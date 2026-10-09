import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalActualEnvelopes

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalTailPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open scoped Topology BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] physicalTime timeSlope rawReader rawReaderContact jointResolvent jointCurrent
  factorialBudget variationBudget sourceJet sourceSlopeJet

private theorem norm_envelope_mul (A B : Op) (a b x y t : ℝ)
    (ha : ‖A‖≤a*Real.exp (x*t)) (hb : ‖B‖≤b*Real.exp (y*t)) :
    ‖A*B‖≤(a*b)*Real.exp ((x+y)*t) :=by
  refine (norm_mul_le A B).trans ((mul_le_mul ha hb (norm_nonneg B) ((norm_nonneg A).trans ha)).trans_eq ?_)
  rw [add_mul,Real.exp_add]
  ring

private theorem norm_envelope_five (A B C D E : Op) (a b c d e x y z w v t : ℝ)
    (hA : ‖A‖≤a*Real.exp (x*t)) (hB : ‖B‖≤b*Real.exp (y*t))
    (hC : ‖C‖≤c*Real.exp (z*t)) (hD : ‖D‖≤d*Real.exp (w*t))
    (hE : ‖E‖≤e*Real.exp (v*t)) :
    ‖A*B*C*D*E‖≤a*b*c*d*e*Real.exp ((x+y+z+w+v)*t) :=
  norm_envelope_mul _ _ _ _ _ _ _
    (norm_envelope_mul _ _ _ _ _ _ _
      (norm_envelope_mul _ _ _ _ _ _ _ (norm_envelope_mul _ _ _ _ _ _ _ hA hB) hC) hD) hE

private theorem constant_envelope (A : Op) (t : ℝ) : ‖A‖≤‖A‖*Real.exp (0*t) :=by simp

private theorem inverseContact_price (R J : Op) : ‖-(R*J*R)‖≤‖R‖*‖J‖*‖R‖ :=by
  rw [norm_neg]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

def rawCoefficient (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F eta*‖jointResolvent (q.p+q.k) q.F q.z 0‖*
    ‖rawReader reader q.p q.F 0‖*‖jointResolvent q.p q.F q.w 0‖*factorialBudget q.p q.F eta

private def genericCoefficient (L R A DA JL JR : Op) (a b u v : ℝ) : ℝ:=
  u*‖L‖*‖A‖*‖R‖*b+a*(‖L‖*‖JL‖*‖L‖)*‖A‖*‖R‖*b+a*‖L‖*‖DA‖*‖R‖*b+
    a*‖L‖*‖A‖*(‖R‖*‖JR‖*‖R‖)*b+a*‖L‖*‖A‖*‖R‖*v

def fiveCoefficient (q : PhysicalResponsePoint) (reader force : Field289) (eta : ℝ) : ℝ:=
  genericCoefficient (jointResolvent (q.p+q.k) q.F q.z 0) (jointResolvent q.p q.F q.w 0)
    (rawReader reader q.p q.F 0) (rawReaderContact reader force q.p q.F)
    (jointCurrent (q.p+q.k) q.F 0 0 force) (jointCurrent q.p q.F 0 0 force)
    (factorialBudget (q.p+q.k) q.F eta) (factorialBudget q.p q.F eta)
    (variationBudget (q.p+q.k) q.F (jointCurrent (q.p+q.k) q.F 0 0 force) eta)
    (variationBudget q.p q.F (jointCurrent q.p q.F 0 0 force) eta)

theorem rawCoefficient_nonnegative (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ)
    (positive : 0<eta) : 0≤rawCoefficient q reader eta :=by
  have L:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have R:=factorialBudget_nonnegative q.p q.F eta positive
  unfold rawCoefficient
  positivity

theorem fiveCoefficient_nonnegative (q : PhysicalResponsePoint) (reader force : Field289) (eta : ℝ)
    (positive : 0<eta) : 0≤fiveCoefficient q reader force eta :=by
  have L:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have R:=factorialBudget_nonnegative q.p q.F eta positive
  have VL:=variationBudget_nonnegative (q.p+q.k) q.F (jointCurrent (q.p+q.k) q.F 0 0 force) eta positive
  have VR:=variationBudget_nonnegative q.p q.F (jointCurrent q.p q.F 0 0 force) eta positive
  unfold fiveCoefficient genericCoefficient
  positivity

theorem rawKernel_price (q : PhysicalResponsePoint) (reader : Field289) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖fiveKernel reader q.p q.k q.F q.z q.w t 0‖≤rawCoefficient q reader eta*Real.exp (4*eta*t) :=by
  have h:=norm_envelope_five _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t
    (actualTime_past (q.p+q.k) q.F eta t positive future)
    (constant_envelope (jointResolvent (q.p+q.k) q.F q.z 0) t)
    (constant_envelope (rawReader reader q.p q.F 0) t)
    (constant_envelope (jointResolvent q.p q.F q.w 0) t)
    (actualTime_future q.p q.F eta t positive future)
  have rate : eta+0+0+0+eta=2*eta:=by ring
  have bound : ‖fiveKernel reader q.p q.k q.F q.z q.w t 0‖≤rawCoefficient q reader eta*Real.exp (2*eta*t):=by
    simpa only [fiveKernel,rawCoefficient,rate] using h
  exact bound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
    (rawCoefficient_nonnegative q reader eta positive))

private theorem generic_five_price (TL TR VL VR L R A DA JL JR : Op) (a b u v eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) (ha : 0≤a) (hb : 0≤b)
    (hTL : ‖TL‖≤a*Real.exp (eta*t)) (hTR : ‖TR‖≤b*Real.exp (eta*t))
    (hVL : ‖VL‖≤u*Real.exp (3*eta*t)) (hVR : ‖VR‖≤v*Real.exp (3*eta*t)) :
    ‖VL*L*A*R*TR+TL*(-(L*JL*L))*A*R*TR+TL*L*DA*R*TR+
      TL*L*A*(-(R*JR*R))*TR+TL*L*A*R*VR‖≤genericCoefficient L R A DA JL JR a b u v*Real.exp (4*eta*t) :=by
  let DL:=-(L*JL*L)
  let DR:=-(R*JR*R)
  have hDL : ‖DL‖≤(‖L‖*‖JL‖*‖L‖)*Real.exp (0*t):=by
    simpa only [DL,zero_mul,Real.exp_zero,mul_one] using inverseContact_price L (JL)
  have hDR : ‖DR‖≤(‖R‖*‖JR‖*‖R‖)*Real.exp (0*t):=by
    simpa only [DR,zero_mul,Real.exp_zero,mul_one] using inverseContact_price R (JR)
  have monotone : Real.exp (2*eta*t)≤Real.exp (4*eta*t):=Real.exp_le_exp.mpr (by nlinarith)
  have first:=norm_envelope_five VL L A R TR
    (u)
    ‖L‖ ‖A‖ ‖R‖ (b) (3*eta) 0 0 0 eta t hVL
    (constant_envelope L t) (constant_envelope A t) (constant_envelope R t) hTR
  have second:=norm_envelope_five TL DL A R TR (a)
    (‖L‖*‖JL‖*‖L‖) ‖A‖ ‖R‖ (b)
    eta 0 0 0 eta t hTL hDL (constant_envelope A t) (constant_envelope R t) hTR
  have middle:=norm_envelope_five TL L DA R TR (a)
    ‖L‖ ‖DA‖ ‖R‖ (b) eta 0 0 0 eta t hTL
    (constant_envelope L t) (constant_envelope DA t) (constant_envelope R t) hTR
  have fourth:=norm_envelope_five TL L A DR TR (a)
    ‖L‖ ‖A‖ (‖R‖*‖JR‖*‖R‖) (b)
    eta 0 0 0 eta t hTL (constant_envelope L t) (constant_envelope A t) hDR hTR
  have fifth:=norm_envelope_five TL L A R VR (a) ‖L‖ ‖A‖ ‖R‖
    (v) eta 0 0 0 (3*eta) t hTL
    (constant_envelope L t) (constant_envelope A t) (constant_envelope R t) hVR
  have hE : eta+0+0+0+eta=2*eta:=by ring
  have hL : 3*eta+0+0+0+eta=4*eta:=by ring
  have hR : eta+0+0+0+3*eta=4*eta:=by ring
  simp only [hL] at first
  simp only [hE] at second middle fourth
  simp only [hR] at fifth
  have n2 : 0≤a*(‖L‖*‖JL‖*‖L‖)*‖A‖*‖R‖*b:=by

    positivity
  have n3 : 0≤a*‖L‖*‖DA‖*‖R‖*b:=by

    positivity
  have n4 : 0≤a*‖L‖*‖A‖*(‖R‖*‖JR‖*‖R‖)*b:=by

    positivity
  have second':=second.trans (mul_le_mul_of_nonneg_left monotone n2)
  have middle':=middle.trans (mul_le_mul_of_nonneg_left monotone n3)
  have fourth':=fourth.trans (mul_le_mul_of_nonneg_left monotone n4)
  change ‖VL*L*A*R*TR+TL*DL*A*R*TR+TL*L*DA*R*TR+TL*L*A*DR*TR+TL*L*A*R*VR‖≤_
  refine (norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add first second')) middle'))
      fourth')) fifth).trans_eq ?_)
  unfold genericCoefficient
  simp only [add_mul]

theorem fiveKernel_price (q : PhysicalResponsePoint) (reader force : Field289) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖fiveDerivative reader force q.p q.k q.F q.z q.w t‖≤
      fiveCoefficient q reader force eta*Real.exp (4*eta*t) :=by
  have h:=generic_five_price
    (physicalTime (q.p+q.k) q.F (-t) 0) (physicalTime q.p q.F t 0)
    (timeSlope force (q.p+q.k) q.F (-t)) (timeSlope force q.p q.F t)
    (jointResolvent (q.p+q.k) q.F q.z 0) (jointResolvent q.p q.F q.w 0)
    (rawReader reader q.p q.F 0) (rawReaderContact reader force q.p q.F)
    (jointCurrent (q.p+q.k) q.F 0 0 force) (jointCurrent q.p q.F 0 0 force)
    (factorialBudget (q.p+q.k) q.F eta) (factorialBudget q.p q.F eta)
    (variationBudget (q.p+q.k) q.F (jointCurrent (q.p+q.k) q.F 0 0 force) eta)
    (variationBudget q.p q.F (jointCurrent q.p q.F 0 0 force) eta) eta t positive future
    (factorialBudget_nonnegative (q.p+q.k) q.F eta positive) (factorialBudget_nonnegative q.p q.F eta positive)
    (actualTime_past (q.p+q.k) q.F eta t positive future) (actualTime_future q.p q.F eta t positive future)
    (actualSlope_past force (q.p+q.k) q.F eta t positive future) (actualSlope_future force q.p q.F eta t positive future)
  unfold fiveCoefficient fiveDerivative
  simp only [jointCurrent_source] at h ⊢
  exact h

def scalarCoefficient (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta : ℝ) (i : Fin 289) : ℝ:=
  ‖responseLeft q‖*‖responseRight q‖*
    (if response then fiveCoefficient q (fieldUnit i) force eta else rawCoefficient q (fieldUnit i) eta)

private theorem sourcePair_price (x y : H) (A : Op) (c : ℝ) (hA : ‖A‖≤c) :
    ‖-inner ℂ x (A y)‖≤‖x‖*‖y‖*c :=by
  rw [norm_neg]
  refine (norm_inner_le_norm x (A y)).trans ?_
  refine (mul_le_mul_of_nonneg_left ((A.le_opNorm y).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg y))) (norm_nonneg x)).trans_eq ?_
  ring

theorem scalarCoefficient_nonnegative (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta : ℝ) (positive : 0<eta) (i : Fin 289) : 0≤ scalarCoefficient q force response eta i :=by
  unfold scalarCoefficient
  split
  · have :=fiveCoefficient_nonnegative q (fieldUnit i) force eta positive
    positivity
  · have :=rawCoefficient_nonnegative q (fieldUnit i) eta positive
    positivity

theorem actualSource_price (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (eta t : ℝ) (positive : 0<eta) (future : 0≤t) (i : Fin 289) :
    ‖(fullSourceJet q force response t i).value‖ ≤ scalarCoefficient q force response eta i*Real.exp (4*eta*t) :=by
  cases response
  · have h:=sourcePair_price (responseLeft q) (responseRight q) _ _ (rawKernel_price q (fieldUnit i) eta t positive future)
    simpa only [fullSourceJet,Bool.false_eq_true,↓reduceIte,sourceJet,negativeJet,pairJet,rawKernelJet_value,
      scalarCoefficient,mul_assoc] using h
  · have h:=sourcePair_price (responseLeft q) (responseRight q) _ _ (fiveKernel_price q (fieldUnit i) force eta t positive future)
    simpa only [fullSourceJet,↓reduceIte,sourceSlopeJet,negativeJet,pairJet,slopeKernelJet_value,
      scalarCoefficient,mul_assoc] using h

end LowEnergy.PreparationVacuumPhysicalTailPrice
