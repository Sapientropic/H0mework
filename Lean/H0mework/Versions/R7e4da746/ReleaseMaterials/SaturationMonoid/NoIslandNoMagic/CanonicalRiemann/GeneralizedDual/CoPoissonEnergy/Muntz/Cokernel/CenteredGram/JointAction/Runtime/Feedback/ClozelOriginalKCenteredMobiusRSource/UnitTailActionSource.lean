import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Contraction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCenteredMobiusRSource.UnitTailActionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalPaPhysicalGreen
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped ENNReal Topology BigOperators
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The native source fibre is distinct from the unit response it realizes. -/
def nativeUnitMuSource (c:BurnolCompletedMellinCoordinate) (j:Nat) : BurnolL2 :=
  -((-2:ℂ)^j) • burnolTateReciprocalL2 (Eq (dividedLogColumn (barC c) j))

def nativeUnitMuRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) : ℂ :=
  if 4 < |x| then -((-2:ℂ)^j)*((|x|:ℝ):ℂ)^(-c.value)*
    (Real.log (|x|/4):ℂ)^j/(j.factorial:ℂ) else 0

private theorem bar_bar (c:BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem full_column_step (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    sourceVolterraResolvent c (Eq (dividedLogColumn (barC c) j))=
      (-2:ℂ) • Eq (dividedLogColumn (barC c) (j+1)) := by
  let column:=dividedLogColumn (barC c) j
  have cutoff:(FiniteMobiusResolventFlux.cutoff q) (Eq column)=Eq column := by
    change Eq (Rq (Eq column))=Eq column
    rw [burnolQuarterRestriction_zeroExtension]
  have right:1/4<(c.value/2).re:=by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have support:=OriginalPrimitiveRankBalance.cutoff_Rplus_source q (by norm_num)
    (c.value/2) right (Eq column)
  rw [cutoff,FiniteMobiusResolventFlux.Rplus_tate _ right] at support
  change Eq (Rq (sourceVolterraResolvent c (Eq column)))=
    sourceVolterraResolvent c (Eq column) at support
  have step: Rq (sourceVolterraResolvent c (Eq column))=
      (-2:ℂ) • dividedLogColumn (barC c) (j+1) := by
    have paid:=quarterStep_log_column (barC c) j
    simpa only [quarterStep,sourceStep,ContinuousLinearMap.comp_apply,bar_bar] using paid
  rw [←support,step,map_smul]

/-- Actual original R advances the native L2 source by one divided-log column. -/
theorem native_unit_source_action (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolDirectRightResolvent (c.value/2) (nativeUnitMuSource c j)=
      nativeUnitMuSource c (j+1) := by
  have tateAction (value:BurnolL2) :
      burnolDirectRightResolvent (c.value/2) (burnolTateReciprocalL2 value)=
        burnolTateReciprocalL2 (sourceVolterraResolvent c value) := by
    change _=burnolTateReciprocalL2 (burnolTateReciprocalL2
      (burnolDirectRightResolvent (c.value/2) (burnolTateReciprocalL2 value)))
    rw [burnolTateReciprocalL2_involutive]
  change (burnolDirectRightResolventCLM c) (-((-2:ℂ)^j) •
    burnolTateReciprocalL2 (Eq (dividedLogColumn (barC c) j)))=_
  rw [map_smul]
  change -((-2:ℂ)^j) • burnolDirectRightResolvent (c.value/2)
    (burnolTateReciprocalL2 (Eq (dividedLogColumn (barC c) j)))=_
  rw [tateAction,full_column_step,map_smul,nativeUnitMuSource,pow_succ]
  module

private def compactColumnRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) : ℝ→ℂ :=
  (symmetricInterval q).indicator (dividedLogRaw (barC c) j)

private theorem compact_column_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    (Eq (dividedLogColumn (barC c) j):ℝ→ℂ)=ᵐ[volume] compactColumnRaw c j := by
  have profile:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (dividedLogColumn_profile (barC c) j)
  filter_upwards [burnolQuarterZeroExtension_coe (dividedLogColumn (barC c) j),profile]
    with x extension raw
  rw [extension]
  unfold compactColumnRaw
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,raw inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem reciprocal_column_raw (c:BurnolCompletedMellinCoordinate) (j:Nat)
    (x:ℝ) (nonzero:x≠0) (boundary:|x|≠4) :
    -((-2:ℂ)^j)*burnolTateReciprocalRaw (compactColumnRaw c j) x=nativeUnitMuRaw c j x := by
  have positive:0 < |x|:=abs_pos.mpr nonzero
  have inverseIncidence:x⁻¹∈symmetricInterval q ↔ 4 < |x| := by
    change -q≤x⁻¹ ∧ x⁻¹≤q ↔ _
    rw [←abs_le,abs_inv,←one_div,div_le_iff₀ positive]
    constructor
    · intro h
      exact lt_of_le_of_ne (by linarith) boundary.symm
    · intro h
      linarith
  unfold burnolTateReciprocalRaw compactColumnRaw nativeUnitMuRaw
  by_cases outside:4 < |x|
  · rw [indicator_of_mem (inverseIncidence.mpr outside),if_pos outside]
    unfold dividedLogRaw SingularCounting.powerRaw
    have coordinate:star (barC c).value=c.value:=star_star c.value
    rw [coordinate,abs_inv]
    have logArgument:q/|x|⁻¹=|x|/4 := by rw [div_inv_eq_mul]; ring
    rw [logArgument]
    have power:((|x|:ℝ):ℂ)⁻¹*((|x|⁻¹:ℝ):ℂ)^(c.value-1)=
        ((|x|:ℝ):ℂ)^(-c.value) := by
      rw [Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg positive.le,←Complex.cpow_neg]
      rw [show ((|x|:ℝ):ℂ)⁻¹=((|x|:ℝ):ℂ)^(-1:ℂ) by
        rw [Complex.cpow_neg,Complex.cpow_one]]
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
      congr 1
      ring
    calc
      _= -((-2:ℂ)^j)*(((|x|:ℝ):ℂ)⁻¹*((|x|⁻¹:ℝ):ℂ)^(c.value-1))*
        (Real.log (|x|/4):ℂ)^j/(j.factorial:ℂ) := by ring
      _=_ := by rw [power]
  · rw [indicator_of_notMem (fun h=>outside (inverseIncidence.mp h)),if_neg outside,mul_zero,mul_zero]

/-- Every native source has its actual whole-axis divided-log tail representative. -/
theorem native_unit_source_profile (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    (nativeUnitMuSource c j:ℝ→ℂ)=ᵐ[volume] nativeUnitMuRaw c j := by
  let value:=Eq (dividedLogColumn (barC c) j)
  have column:=compact_column_read c j
  have rawNative:MemLp (compactColumnRaw c j) 2 volume:=
    (memLp_congr_ae column).mp (Lp.memLp value)
  have tate:=(burnolTateReciprocalL2_coeFn value).trans
    (burnolTateReciprocalRaw_ae_congr (Lp.memLp value) rawNative column)
  filter_upwards [Lp.coeFn_smul (-((-2:ℂ)^j)) (burnolTateReciprocalL2 value),
    tate,volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x scalar raw nonzero positiveBoundary negativeBoundary
  change (-((-2:ℂ)^j) • burnolTateReciprocalL2 value:BurnolL2) x=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,raw]
  apply reciprocal_column_raw c j x nonzero
  intro equal
  rcases (abs_eq (by norm_num : (0:ℝ)≤4)).mp equal with eq|eq
  · exact positiveBoundary eq
  · exact negativeBoundary eq

theorem native_unit_source_zero (c:BurnolCompletedMellinCoordinate) :
    (nativeUnitMuSource c 0:ℝ→ℂ)=ᵐ[volume] burnolRadiusUnitTailRaw c.value 4 := by
  filter_upwards [native_unit_source_profile c 0] with x raw
  rw [raw]
  simp only [nativeUnitMuRaw,burnolRadiusUnitTailRaw,pow_zero,neg_one_mul,
    Nat.factorial_zero,Nat.cast_one,div_one,mul_one]

namespace Canonical
export OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
  (rawIterate actualIterate actual_iterate_power iterate_raw_read iterate_raw_native iterate_inverse_R_action)
end Canonical

/-- This is the native representative of the actual iterated unit response, not its source fibre. -/
def unitResponseRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) : ℝ→ℂ :=
  Canonical.rawIterate c (unitRaw c) j

def unitResponseField (c:BurnolCompletedMellinCoordinate) (j:Nat) : BurnolL2 :=
  Canonical.actualIterate c (burnolUnitTailResponse c 4) j

private theorem original_unit_even (c:BurnolCompletedMellinCoordinate) :
    reflectL2 (burnolUnitTailResponse c 4)=burnolUnitTailResponse c 4 :=
  burnolReflectL2_eq_of_even_raw _ _ (unitRaw_read c) (fun x=>by
    simp only [unitRaw,burnolUnitTailDirichletRaw,burnolUnitTailDirichletChannels,abs_neg])

private theorem original_unit_gap (c:BurnolCompletedMellinCoordinate) :
    ∀{x:ℝ},|x|≤q→unitRaw c x=unitRaw c 0 := by
  intro x small
  rw [unitRaw_gap c (by linarith),unitRaw_zero]

theorem actual_unit_response_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    (unitResponseField c j:ℝ→ℂ)=ᵐ[volume]unitResponseRaw c j :=
  Canonical.iterate_raw_read c (burnolUnitTailResponse c 4) (unitRaw c)
    (unitRaw_read c) (original_unit_gap c) (original_unit_even c) j

theorem actual_unit_response_native (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    MemLp (unitResponseRaw c j) 2 volume :=
  (memLp_congr_ae (actual_unit_response_read c j)).mp (Lp.memLp _)

private theorem unit_response_raw_even (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    unitResponseRaw c j (-x)=unitResponseRaw c j x := by
  cases j with
  | zero => simp only [unitResponseRaw,Canonical.rawIterate,unitRaw,burnolUnitTailDirichletRaw,
      burnolUnitTailDirichletChannels,abs_neg]
  | succ j => simp only [unitResponseRaw,Canonical.rawIterate,sourceRRaw,abs_neg]

private theorem unit_response_inverse_even (c:BurnolCompletedMellinCoordinate) (j:Nat) (t:ℝ) :
    burnolCenteredMobiusInverse (unitResponseRaw c j) (-t)=
      burnolCenteredMobiusInverse (unitResponseRaw c j) t := by
  unfold burnolCenteredMobiusInverse
  apply tsum_congr
  intro n
  simp only [neg_div,unit_response_raw_even]

theorem native_unit_raw_inside (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {x:ℝ} (small:|x|≤4) : nativeUnitMuRaw c j x=0 := by
  simp only [nativeUnitMuRaw,if_neg (not_lt.mpr small)]

/-- Actual unit R-iterates have precisely the native divided-log Mobius source generated above. -/
theorem original_unit_power_inverse (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolCenteredMobiusInverse (unitResponseRaw c j)=ᵐ[volume]nativeUnitMuRaw c j := by
  induction j with
  | zero =>
    filter_upwards [native_unit_source_profile c 0,native_unit_source_zero c] with x profile unit
    exact (original_unit_inverse_source c x).trans (unit.symm.trans profile)
  | succ j previous =>
    have sourceGap:∀{x:ℝ},|x|≤q→nativeUnitMuRaw c j x=nativeUnitMuRaw c j 0 := by
      intro x small
      rw [native_unit_raw_inside c j (by linarith),native_unit_raw_inside c j (by norm_num)]
    have action:=actual_R_positive_read c (nativeUnitMuSource c j) (nativeUnitMuRaw c j)
      (native_unit_source_profile c j) sourceGap
    rw [native_unit_source_action] at action
    have positive:∀ᵐ x:ℝ ∂volume,0<x→
        burnolCenteredMobiusInverse (unitResponseRaw c (j+1)) x=nativeUnitMuRaw c (j+1) x := by
      filter_upwards [action,native_unit_source_profile c (j+1)] with x actual profile pos
      have sourceAction:=Canonical.iterate_inverse_R_action c (burnolUnitTailResponse c 4)
        (unitRaw c) (unitRaw_read c) (original_unit_gap c) (original_unit_even c) j x pos
      change burnolCenteredMobiusInverse (unitResponseRaw c (j+1)) x=
        -2*(x:ℂ)^(-c.value)*(∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1)*
          burnolCenteredMobiusInverse (unitResponseRaw c j) v) at sourceAction
      have integralRead:(∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1)*
          burnolCenteredMobiusInverse (unitResponseRaw c j) v)=
          ∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1)*nativeUnitMuRaw c j v := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [previous] with v hv _
        rw [hv]
      calc
        _= -2*(x:ℂ)^(-c.value)*(∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1)*nativeUnitMuRaw c j v) := by
          rw [sourceAction,integralRead]
        _=sourceRRaw c (nativeUnitMuRaw c j) x := by
          unfold sourceRRaw weightedCentered
          rw [abs_of_pos pos,native_unit_raw_inside c j (by norm_num)]
          simp only [mul_zero,zero_div,sub_zero,zero_sub]
          ring
        _=nativeUnitMuRaw c (j+1) x := (actual pos).symm.trans profile
    have reflected:=(Measure.measurePreserving_neg (volume:Measure ℝ)).quasiMeasurePreserving.ae positive
    filter_upwards [positive,reflected,volume.ae_ne (0:ℝ)] with x first second nonzero
    by_cases pos:0<x
    · exact first pos
    · have negpos:0< -x:=by
        have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nonzero
        linarith
      calc
        _=burnolCenteredMobiusInverse (unitResponseRaw c (j+1)) (-x):=
          (unit_response_inverse_even c (j+1) x).symm
        _=nativeUnitMuRaw c (j+1) (-x):=second negpos
        _=nativeUnitMuRaw c (j+1) x:=by simp only [nativeUnitMuRaw,abs_neg]

/-- The original signed unit family is the same iterated response, by its source definition. -/
theorem original_unitPower_field (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (j:Nat) :
    OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half j=
      unitResponseField (burnolDivisionZeroCompletedMellinCoordinate observation half.down) j := by
  rw [unitResponseField,Canonical.actual_iterate_power]
  rfl

theorem original_unitPower_raw (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (j:Nat) :
    (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half j:ℝ→ℂ)=ᵐ[volume]
      unitResponseRaw (burnolDivisionZeroCompletedMellinCoordinate observation half.down) j := by
  rw [original_unitPower_field]
  exact actual_unit_response_read _ j

/-- The same original unit family has the generated native source, with no identification of the two L2 vectors. -/
theorem original_unitPower_native_source (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (j:Nat) :
    burnolCenteredMobiusInverse
      (unitResponseRaw (burnolDivisionZeroCompletedMellinCoordinate observation half.down) j)=ᵐ[volume]
      (nativeUnitMuSource (burnolDivisionZeroCompletedMellinCoordinate observation half.down) j:ℝ→ℂ) :=
  (original_unit_power_inverse _ j).trans (native_unit_source_profile _ j).symm

end OriginalKCenteredMobiusRSource.UnitTailActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
