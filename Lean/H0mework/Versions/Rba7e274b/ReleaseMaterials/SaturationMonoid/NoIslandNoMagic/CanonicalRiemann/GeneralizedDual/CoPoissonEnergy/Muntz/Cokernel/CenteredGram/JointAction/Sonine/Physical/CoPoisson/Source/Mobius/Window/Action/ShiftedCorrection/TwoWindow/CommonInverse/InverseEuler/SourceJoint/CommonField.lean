import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Forcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing InverseEuler
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)

private theorem upper_dilated_band_restriction_zero (h : ℝ) (nonnegative : 0≤h)
    (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    burnolQuarterRestriction (burnolMultiplicativeDilation (-h/2) field)=0 := by
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-h/2)*x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp (-h/2)) (Real.exp_ne_zero _))
  have lower : lowerRadius h=Real.exp (-h/2)*q := by
    unfold lowerRadius FixedWindowFourierReaction.actualRadius
    rw [show (-h)/2=-h/2 by ring]
    ring
  have notEndpointAE : ∀ᵐ x:ℝ ∂volume,x≠q := by simp [ae_iff,measure_singleton]
  have actualZero : (burnolMultiplicativeDilation (-h/2) field:ℝ→ℂ)=ᵐ[μq] (fun _=>0) := by
    filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q),
      ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-h/2) field),
      ae_restrict_of_ae (qmp.ae fieldRead),ae_restrict_of_ae notEndpointAE]
      with x inside dilated actual notEndpoint
    have before : Real.exp (-h/2)*x<lowerRadius h := by
      rw [lower]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_ne inside.2 notEndpoint) (Real.exp_pos _)
    have outside : Real.exp (-h/2)*x∉sourceBand h := by
      unfold sourceBand
      rw [uIcc_of_le (source_radii_ordered h nonnegative)]
      exact fun belongs=>not_le_of_gt before belongs.1
    rw [dilated]
    unfold burnolL2RawNormalizedDilation
    rw [actual,indicator_of_notMem outside,mul_zero]
  have restrictedRead : (burnolQuarterRestriction (burnolMultiplicativeDilation (-h/2) field):ℝ→ℂ)=ᵐ[μq]
      (burnolMultiplicativeDilation (-h/2) field:ℝ→ℂ) :=
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) _
  apply Lp.ext
  filter_upwards [restrictedRead,actualZero,Lp.coeFn_zero ℂ 2 μq] with x restrictRead zeroRead zeroValue
  rw [restrictRead,zeroRead,zeroValue]
  rfl

private theorem evenPart_restriction_zero (field : BurnolL2) (zero : burnolQuarterRestriction field=0) :
    burnolQuarterRestriction (burnolAmbientEvenPart field)=0 := by
  unfold burnolAmbientEvenPart
  have reflected : burnolQuarterRestriction (reflectL2 field)=reflectRestricted q (burnolQuarterRestriction field) :=
    restrictToInterval_reflectL2 q field
  rw [map_smul,map_add,reflected,zero,map_zero,zero_add,smul_zero]

private theorem evenPart_add (left right : BurnolL2) :
    burnolAmbientEvenPart (left+right)=burnolAmbientEvenPart left+burnolAmbientEvenPart right := by
  unfold burnolAmbientEvenPart
  rw [map_add]
  module

def upperSourceField (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolAmbientEvenPart (burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2))+
    fourierL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))))

theorem upper_source_both_restrictions (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    Constructor.zeroMean (burnolQuarterRestriction (upperSourceField coordinate h))=(sourceColumns coordinate h).2.1 ∧
    Constructor.zeroMean (burnolQuarterRestriction (fourierL2 (upperSourceField coordinate h)))=(sourceColumns coordinate h).2.2 := by
  have sourceB:=upper_dilated_band_restriction_zero h nonnegative (bBand coordinate h (-h/2))
    (bLeg coordinate (-h/2)) (bBand_raw coordinate h (-h/2))
  have sourceP:=upper_dilated_band_restriction_zero h nonnegative (pBand coordinate h (-h/2))
    (pLeg coordinate (-h/2)) (pBand_raw coordinate h (-h/2))
  have zeroP:=evenPart_restriction_zero _ sourceP
  constructor
  · unfold upperSourceField
    rw [evenPart_add,map_add,zeroP,zero_add]
    simp only [sourceColumns,cotestColumn,show -(h/2)=-h/2 by ring]
  · unfold upperSourceField
    rw [fourierL2_burnolAmbientEvenPart,map_add,fourierL2_fourierL2,evenPart_add,map_add]
    have reflectedZero : burnolQuarterRestriction
        (burnolAmbientEvenPart (reflectL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2)))))=0 := by
      apply evenPart_restriction_zero
      have reflected : burnolQuarterRestriction
          (reflectL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))))=
          reflectRestricted q (burnolQuarterRestriction (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2)))) :=
        restrictToInterval_reflectL2 q _
      rw [reflected,sourceB,map_zero]
    rw [reflectedZero,add_zero]
    simp only [sourceColumns,cotestColumn,show -(h/2)=-h/2 by ring]

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
