import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
open scoped Topology
open private tail_difference tate_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa
open private outgoing_power_compact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open private compact_annulus_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
local notation "q"=>(1/4:ℝ)
local notation "A"=>sourceAnnulusCut
local notation "E"=>burnolQuarterZeroExtension
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem tail_below (d:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (x:ℝ) (positive:0<x) (below:x<q):
    burnolRadiusMellinTailEvaluator x positive d.value d.rightHalf (A value)=
      burnolRadiusMellinTailEvaluator q (by norm_num) d.value d.rightHalf (A value):=by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,burnolRadiusMellinTailEvaluator_eq_integral,
    ←integral_indicator measurableSet_Ioi,←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [sourceAnnulusCut_coeFn value] with u cut
  by_cases beyond:q<u
  · rw [indicator_of_mem (show u∈Ioi x from lt_trans below beyond),indicator_of_mem (show u∈Ioi q from beyond)]
  · rw [indicator_of_notMem (show u∉Ioi q from beyond)]
    by_cases after:x<u
    · have positiveU:0<u:=lt_trans positive after
      have outside:¬(q < |u| ∧ |u|≤4):=by
        rw [abs_of_pos positiveU]
        exact fun h=>beyond h.1
      rw [indicator_of_mem (show u∈Ioi x from after),cut,if_neg outside,mul_zero]
    · rw [indicator_of_notMem (show u∉Ioi x from after)]

private theorem tail_above (d:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (x:ℝ) (beyond:4<x):
    burnolRadiusMellinTailEvaluator x (by linarith) d.value d.rightHalf (A value)=0:=by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (sourceAnnulusCut_coeFn value),ae_restrict_mem measurableSet_Ioi]
    with u cut after
  change x<u at after
  have positive:0<u:=by linarith
  rw [cut,if_neg (by rw [abs_of_pos positive];exact fun h=>not_le.mpr (lt_trans beyond after) h.2),mul_zero]
  rfl

def annulusCross (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  A (sourceVolterraResolvent (barC c) (tateSource c j))-
    sourceVolterraResolvent (barC c) (A (tateSource c j))

/-- Both true source cutcrosses survive; the old compact H−B stock contributes to neither. -/
theorem actual_native_cross (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    annulusCross c j=
      A (sourceVolterraResolvent (barC c)
        (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)))-
      sourceVolterraResolvent (barC c)
        (A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c))):=by
  rw [annulusCross,actual_native_annulus,actual_tate_outgoing,actual_native_source]
  simp only [map_add]
  have compact:=compact_annulus_zero _ (outgoing_power_compact (barC c) (nativeCompact c) (j+1))
  rw [pow_succ',mul_apply_eq_comp] at compact
  rw [compact,zero_add]

theorem actual_cross_even (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    reflectL2 (annulusCross c j)=annulusCross c j:=by
  have sourceEven:=tate_even c j
  have movedEven:reflectL2 (sourceVolterraResolvent (barC c) (tateSource c j))=
      sourceVolterraResolvent (barC c) (tateSource c j):=by
    rw [sourceVolterraResolvent_reflect,sourceEven]
  rw [annulusCross,map_sub,sourceAnnulusCut_even _ movedEven,sourceVolterraResolvent_reflect,
    sourceAnnulusCut_even _ sourceEven]

/-- The actual lower and upper crossing stocks are separate source moments, at every original order. -/
theorem actual_cross_source_profile (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    ∀ᵐx:ℝ∂volume,∀_positive:0<x,
      annulusCross c j x=if x<q then
        (2:ℂ)*(x:ℂ)^((barC c).value-1)*
          burnolRadiusMellinTailEvaluator q (by norm_num) (barC c).value (barC c).rightHalf
            (A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)))
      else if x<4 then
        (-2:ℂ)*(x:ℂ)^((barC c).value-1)*
          burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
            (((sourceVolterraResolvent (barC c))^j) (nativeReturn c))
      else 0:=by
  filter_upwards [Lp.coeFn_sub (A (sourceVolterraResolvent (barC c) (tateSource c j)))
      (sourceVolterraResolvent (barC c) (A (tateSource c j))),
    sourceAnnulusCut_coeFn (sourceVolterraResolvent (barC c) (tateSource c j)),
    sourceVolterraResolvent_positive_profile (barC c) (tateSource c j),
    sourceVolterraResolvent_positive_profile (barC c) (A (tateSource c j)),
    volume.ae_ne q,volume.ae_ne (4:ℝ)] with x subtraction cut full finite notQuarter notFour positive
  change (A (sourceVolterraResolvent (barC c) (tateSource c j))-
    sourceVolterraResolvent (barC c) (A (tateSource c j))) x=_
  rw [subtraction,Pi.sub_apply,cut,abs_of_pos positive]
  by_cases below:x<q
  · rw [if_neg (fun h=>not_lt_of_ge below.le h.1),if_pos below,finite positive,
      tail_below (barC c) (tateSource c j) x positive below,actual_native_annulus]
    ring
  · have above:q<x:=lt_of_le_of_ne (le_of_not_gt below) notQuarter.symm
    rw [if_neg below]
    by_cases before:x<4
    · rw [if_pos ⟨above,before.le⟩,if_pos before,full positive,finite positive]
      have tail:=tail_difference (barC c) (tateSource c j) x ⟨above,before⟩
      rw [map_sub,actual_native_upper_tail] at tail
      linear_combination (-2*(x:ℂ)^((barC c).value-1))*tail
    · have beyond:4<x:=lt_of_le_of_ne (le_of_not_gt before) notFour.symm
      rw [if_neg (fun h=>not_le.mpr beyond h.2),if_neg before,finite positive,
        tail_above (barC c) (tateSource c j) x beyond,mul_zero,sub_self]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
