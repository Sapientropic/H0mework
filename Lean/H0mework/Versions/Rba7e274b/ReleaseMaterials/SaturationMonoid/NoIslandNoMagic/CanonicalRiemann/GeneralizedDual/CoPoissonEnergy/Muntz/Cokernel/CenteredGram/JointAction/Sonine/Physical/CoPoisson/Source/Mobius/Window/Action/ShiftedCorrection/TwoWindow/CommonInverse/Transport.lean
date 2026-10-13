import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Columns
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)

def whole (state : BurnolQuarterMeanZeroCarrier) : BurnolL2 :=
  burnolQuarterZeroExtension (state:BurnolQuarterIntervalL2)

theorem whole_even (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) : reflectL2 (whole state)=whole state := by
  unfold whole burnolQuarterZeroExtension
  rw [burnolRadiusZeroExtension_reflect,even]

theorem evenPart_pairing (source field : BurnolL2) (even : reflectL2 source=source) :
    inner ℂ source (burnolAmbientEvenPart field)=inner ℂ source field := by
  have pair:=reflectL2.inner_map_map (reflectL2 source) field
  rw [reflectL2_reflectL2,even] at pair
  unfold burnolAmbientEvenPart
  rw [inner_smul_right,inner_add_right,pair]
  ring

theorem fullFourier_pairing (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) (field : BurnolL2) :
    inner ℂ (fourierL2 (whole state)) field=inner ℂ (whole state) (fourierL2 field) := by
  have twice : fourierL2 (fourierL2 (whole state))=whole state := by
    rw [fourierL2_fourierL2,whole_even state even]
  have paired:=fourierL2.inner_map_map (fourierL2 (whole state)) field
  rw [twice] at paired
  exact paired.symm

theorem quarter_cotest_pairing (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) (scale : ℝ) (field : BurnolL2) :
    inner ℂ (burnolMultiplicativeDilation scale (fourierL2 (whole state))) field=
      inner ℂ state (cotestColumn scale field) := by
  have inverse:= (burnolMultiplicativeDilation scale).inner_map_eq_flip (fourierL2 (whole state)) field
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at inverse
  rw [inverse,fullFourier_pairing state even]
  rw [← evenPart_pairing (whole state) (fourierL2 (burnolMultiplicativeDilation (-scale) field))
    (whole_even state even)]
  unfold whole cotestColumn
  have extension : burnolQuarterZeroExtension=ContinuousLinearMap.adjoint burnolQuarterRestriction := rfl
  rw [extension,ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (state:BurnolQuarterIntervalL2) _=
    inner ℂ (state:BurnolQuarterIntervalL2) (Constructor.zeroMean _:BurnolQuarterIntervalL2)
  exact ((burnolQuarterMeanZeroClosedFace.toSubmodule).inner_orthogonalProjectionOnto_eq_of_mem_left state _).symm

theorem bBand_raw (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    (bBand coordinate h scale:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (bLeg coordinate scale) :=
  MemLp.coeFn_toLp _
theorem pBand_raw (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    (pBand coordinate h scale:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (pLeg coordinate scale) :=
  MemLp.coeFn_toLp _

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
