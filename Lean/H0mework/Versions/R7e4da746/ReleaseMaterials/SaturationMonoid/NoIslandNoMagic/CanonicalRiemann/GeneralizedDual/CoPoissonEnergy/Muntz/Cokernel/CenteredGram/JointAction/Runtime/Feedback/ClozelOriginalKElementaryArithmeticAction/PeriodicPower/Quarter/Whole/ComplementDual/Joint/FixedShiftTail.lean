import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusContact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open scoped Topology InnerProductSpace
open private native_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

def fixedShift:ℝ:=Real.log stageZeroSonineQ
def fixedRadius:ℝ:=4*Real.exp (-fixedShift)
theorem fixed_radius_positive:0<fixedRadius:=mul_pos (by norm_num) (Real.exp_pos _)

private theorem conjugate_character (d:BurnolCompletedMellinCoordinate) (h:ℝ):
    star (fullMellinTranslationCharacter (star d.value) h)=fullMellinTranslationCharacter d.value h:=by
  change (starRingEnd ℂ) (Complex.exp (((1/2:ℂ)-(starRingEnd ℂ) d.value)*(h:ℂ)))=_
  rw [←Complex.exp_conj]
  congr 1
  norm_num [map_ofNat]

private theorem outward_dilation (d:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2):
    sourceVolterraResolvent d (burnolMultiplicativeDilation h value)=
      burnolMultiplicativeDilation h (sourceVolterraResolvent d value):=by
  unfold sourceVolterraResolvent
  simp only [ContinuousLinearMap.comp_apply]
  change burnolTateReciprocalL2 (burnolDirectRightResolvent (d.value/2)
    (burnolTateReciprocalL2 (burnolMultiplicativeDilation h value)))=
      burnolMultiplicativeDilation h (burnolTateReciprocalL2
        (burnolDirectRightResolvent (d.value/2) (burnolTateReciprocalL2 value)))
  have inverse:burnolTateReciprocalL2 (burnolMultiplicativeDilation h value)=
      burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 value):=by
    simpa only [neg_neg] using (burnolTateReciprocalL2_dilation_inverse (-h) value).symm
  rw [inverse,burnolDirectRightResolvent_dilation,burnolTateReciprocalL2_dilation_inverse]

private theorem outward_power_dilation (d:BurnolCompletedMellinCoordinate) (h:ℝ) (j:ℕ) (value:BurnolL2):
    ((sourceVolterraResolvent d)^j) (burnolMultiplicativeDilation h value)=
      burnolMultiplicativeDilation h (((sourceVolterraResolvent d)^j) value):=by
  induction j with
  | zero => rfl
  | succ j previous =>
    rw [pow_succ',mul_apply_eq_comp,previous,outward_dilation]
    rfl

/-- The fixed moving endpoint is read by the same native log source, after actual dilation. -/
theorem actual_fixed_tail_bank (d:BurnolCompletedMellinCoordinate) (j:ℕ)
    (value:BurnolL2) (even:reflectL2 value=value):
    burnolRadiusMellinTailEvaluator fixedRadius fixed_radius_positive d.value d.rightHalf
      (((sourceVolterraResolvent d)^j) value)=
      (fullMellinTranslationCharacter d.value fixedShift)⁻¹*
        (((-2:ℂ)^j/(j.factorial:ℂ))*
          (∫x:ℝ in Ioi 4,(x:ℂ)^(-d.value)*(Real.log (x/4):ℂ)^j*
            burnolMultiplicativeDilation (-fixedShift) value x)):=by
  have moved:=congrArg (fun kernel:BurnolL2=>inner ℂ kernel (((sourceVolterraResolvent d)^j) value))
    (burnolRadiusMellinTail_dilation (by norm_num:(0:ℝ)<4) d fixedShift)
  have flip (x y:BurnolL2):inner ℂ (burnolMultiplicativeDilation fixedShift x) y=
      inner ℂ x (burnolMultiplicativeDilation (-fixedShift) y):=by
    have actual:=(burnolMultiplicativeDilation fixedShift).inner_map_eq_flip x y
    rwa [←burnolMultiplicativeDilation_neg_eq_symm] at actual
  rw [flip,inner_smul_left,starRingEnd_apply,conjugate_character,←outward_power_dilation] at moved
  change burnolRadiusMellinTailEvaluator 4 (by norm_num) d.value d.rightHalf
    (((sourceVolterraResolvent d)^j) (burnolMultiplicativeDilation (-fixedShift) value))=
      fullMellinTranslationCharacter d.value fixedShift*
        burnolRadiusMellinTailEvaluator fixedRadius fixed_radius_positive d.value d.rightHalf
          (((sourceVolterraResolvent d)^j) value) at moved
  have movedEven:reflectL2 (burnolMultiplicativeDilation (-fixedShift) value)=
      burnolMultiplicativeDilation (-fixedShift) value:=by
    rw [reflectL2_burnolMultiplicativeDilation,even]
  rw [actual_outgoing_log_bank _ _ _ movedEven] at moved
  calc
    _=(fullMellinTranslationCharacter d.value fixedShift)⁻¹*
        (fullMellinTranslationCharacter d.value fixedShift*
          burnolRadiusMellinTailEvaluator fixedRadius fixed_radius_positive d.value d.rightHalf
            (((sourceVolterraResolvent d)^j) value)):=by
      rw [inv_mul_cancel_left₀ (show fullMellinTranslationCharacter d.value fixedShift≠0
        from Complex.exp_ne_zero _)]
    _=_:=by rw [←moved]

theorem actual_fixed_native_tail_bank (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolRadiusMellinTailEvaluator fixedRadius fixed_radius_positive (barC c).value (barC c).rightHalf
      (((sourceVolterraResolvent (barC c))^j) (nativeReturn c))=
      (fullMellinTranslationCharacter (star c.value) fixedShift)⁻¹*
        (((-2:ℂ)^j/(j.factorial:ℂ))*
          (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^j*
            burnolMultiplicativeDilation (-fixedShift) (nativeReturn c) x)):=
  actual_fixed_tail_bank (barC c) j (nativeReturn c) (native_even c)

/-- The actual fixed-shift source retains both original Fourier legs before taking the tail. -/
theorem actual_fixed_native_word (c:BurnolCompletedMellinCoordinate):
    burnolMultiplicativeDilation (-fixedShift) (nativeReturn c)=
      ForcingPrimitive.leadingCoefficient c • fourierL2
        (burnolMultiplicativeDilation fixedShift
          (burnolQuarterZeroExtension (burnolMeanZeroTruncatedFourier (logBFirst c 0):BurnolQuarterIntervalL2)))-
      fourierL2 (burnolMultiplicativeDilation fixedShift (burnolCompletedMellinRieszVector c:BurnolL2)):=by
  rw [nativeReturn,map_sub,map_smul,←fourierL2_burnolMultiplicativeDilation,
    ←fourierL2_burnolMultiplicativeDilation]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
