import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCompactPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKCenteredMobiusRSource OriginalKCenteredMobiusRSource.UnitTailActionSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedTail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass
open scoped Topology InnerProductSpace
open private native_mean from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass
local notation "R"=>burnolDirectRightResolventCLM
local notation "D"=>burnolMultiplicativeDilation
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "q"=>(1/4:ℝ)
local notation "Cq"=>intervalConstant q
local notation "meanQ"=>burnolQuarterMeanCoefficient

def unitCoefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  (-2/c.value)^j*((4:ℂ)^(-c.value)/c.value)

private theorem source_gap_four (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (gap:∀{x:ℝ},|x|≤4 → raw x=raw 0) {x:ℝ} (inside:|x|≤4):
    sourceRRaw c raw x=-2*raw 0/c.value:=by
  have iz:(∫v:ℝ in 0..|x|,weightedCentered c raw v)=0:=by
    rw [intervalIntegral.integral_of_le (abs_nonneg x)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    unfold weightedCentered
    rw [gap (by rw [abs_of_nonneg hv.1.le];exact hv.2.trans inside),sub_self,mul_zero]
  rw [sourceRRaw,iz,mul_zero,sub_zero]

private theorem iterate_gap_four (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    ∀{x:ℝ},|x|≤4→unitResponseRaw c j x=unitResponseRaw c j 0:=by
  induction j with
  | zero=>
    intro x inside
    change unitRaw c x=unitRaw c 0
    rw [unitRaw_gap c inside,unitRaw_zero]
  | succ j previous=>
    intro x inside
    change sourceRRaw c (unitResponseRaw c j) x=sourceRRaw c (unitResponseRaw c j) 0
    rw [source_gap_four c _ previous inside,sourceRRaw_zero]

private theorem iterate_zero (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    unitResponseRaw c j 0=unitCoefficient c j:=by
  induction j with
  | zero=>simpa only [unitResponseRaw,Canonical.rawIterate,unitCoefficient,pow_zero,one_mul] using unitRaw_zero c
  | succ j previous=>
    change sourceRRaw c (unitResponseRaw c j) 0=_
    rw [sourceRRaw_zero,previous]
    simp only [unitCoefficient,pow_succ]
    ring

/-- The actual full Unit powers keep their independently counted constant gap all the way to radius four. -/
theorem actual_unit_four_gap (c:BurnolCompletedMellinCoordinate) (j:ℕ) {x:ℝ} (inside:|x|≤4):
    unitResponseRaw c j x=unitCoefficient c j:=
  (iterate_gap_four c j inside).trans (iterate_zero c j)

/-- A moved compact head reads the actual full Unit gap before any physical projection. -/
theorem actual_unit_quarter_dilation (c:BurnolCompletedMellinCoordinate) (j:ℕ) (shift:ℝ)
    (inside:Real.exp shift*q≤4):
    Rq (D shift (((R c)^j) (burnolUnitTailResponse c 4)))=
      ((Real.exp (shift/2):ℂ)*unitCoefficient c j) • Cq:=by
  have native:=actual_unit_response_read c j
  rw [unitResponseField,Canonical.actual_iterate_power] at native
  have qmp:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp shift*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume:Measure ℝ))
        (r:=Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (D shift (((R c)^j) (burnolUnitTailResponse c 4))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift (((R c)^j) (burnolUnitTailResponse c 4))),
    ae_restrict_of_ae (qmp.ae native),ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (shift/2):ℂ)*unitCoefficient c j) Cq,
    intervalConstant_coeFn q] with x restriction dilation source small scalar constant
  have scaled:|Real.exp shift*x|≤4:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos shift)]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr small) (Real.exp_pos shift).le).trans inside
  change Rq (D shift (((R c)^j) (burnolUnitTailResponse c 4))) x=_
  rw [show Rq (D shift (((R c)^j) (burnolUnitTailResponse c 4))) x=
    D shift (((R c)^j) (burnolUnitTailResponse c 4)) x from restriction,dilation,scalar]
  change (Real.exp (shift/2):ℂ)*(((R c)^j) (burnolUnitTailResponse c 4)) (Real.exp shift*x)=
    ((Real.exp (shift/2):ℂ)*unitCoefficient c j)*Cq x
  rw [source,actual_unit_four_gap c j scaled,constant,mul_one]

private theorem inner_mean (state:Hq):inner ℂ Cq state=meanQ state/2:=by
  have square:=burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)
  have realRaw:‖Cq‖^2=2*q:=by exact_mod_cast square
  have realSquare:‖Cq‖^2=(1/2:ℝ):=by linarith [realRaw]
  unfold burnolQuarterMeanCoefficient
  rw [realSquare]
  norm_num
  ring

/-- Both moving compact contacts retain exactly H's complete ordinary mean, including the original B cancellation. -/
theorem actual_native_compact_unit_price (c:BurnolCompletedMellinCoordinate) (j:ℕ) (shift:ℝ)
    (inside:Real.exp (-shift)*q≤4):
    inner ℂ (((R c)^j) (burnolUnitTailResponse c 4)) (D shift (E (nativeCompact c)))=
      star ((Real.exp (-shift/2):ℂ)*unitCoefficient c j)*(meanQ (Rq (quarterWave c))/2):=by
  have moved:=(D (-shift)).inner_map_eq_flip (((R c)^j) (burnolUnitTailResponse c 4)) (E (nativeCompact c))
  rw [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at moved
  rw [←moved]
  have restricted:=ContinuousLinearMap.adjoint_inner_right Rq
    (D (-shift) (((R c)^j) (burnolUnitTailResponse c 4))) (nativeCompact c)
  change inner ℂ (D (-shift) (((R c)^j) (burnolUnitTailResponse c 4))) (E (nativeCompact c))=
    inner ℂ (Rq (D (-shift) (((R c)^j) (burnolUnitTailResponse c 4)))) (nativeCompact c) at restricted
  rw [restricted,actual_unit_quarter_dilation c j (-shift) inside,inner_smul_left,
    inner_mean,native_mean]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCompactPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
