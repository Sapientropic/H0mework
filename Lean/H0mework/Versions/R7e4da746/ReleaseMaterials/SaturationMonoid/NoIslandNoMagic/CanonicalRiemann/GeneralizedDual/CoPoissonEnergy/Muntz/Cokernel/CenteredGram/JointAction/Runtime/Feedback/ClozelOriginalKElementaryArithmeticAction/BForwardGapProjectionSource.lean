import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.BForwardEndpointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBForwardGapProjectionSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalKExteriorCoPoissonAction OriginalKFiniteOrderRelease
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKFiniteOrderRelease.QuarterSourceCommutator OriginalKFiniteOrderRelease.GenericSourceStepBAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "BI" => burnolMeanZeroBlockInverse
local notation "mu" => burnolQuarterMeanCoefficient
local notation "Rq" => burnolQuarterRestriction
open private position_read fourier_read
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

private theorem physical_fibres (value:BurnolPaAmbientCarrier) :
    b (value:BurnolL2)=0 ∧ d (value:BurnolL2)=0 := by
  have even:reflectL2 (value:BurnolL2)=value:=mem_evenL2ClosedFace_iff.mp value.property.2
  have position:X (value:BurnolL2)=0 := by
    rw [position_read _ even]
    apply Subtype.ext
    change burnolQuarterMeanZeroProjection (Rq (value:BurnolL2))=0
    exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr value.property.1.1
  have fourier:Y (value:BurnolL2)=0 := by
    rw [fourier_read _ even]
    apply Subtype.ext
    change burnolQuarterMeanZeroProjection (Rq (F (value:BurnolL2)))=0
    exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr value.property.1.2
  have first:b (value:BurnolL2)=0 := by
    change BI (X (value:BurnolL2)-burnolMeanZeroTruncatedFourier (Y (value:BurnolL2)))=0
    rw [position,fourier,map_zero,sub_zero,map_zero]
  refine ⟨first,?_⟩
  change Y (value:BurnolL2)-burnolMeanZeroTruncatedFourier (b (value:BurnolL2))=0
  rw [fourier,first,map_zero,sub_zero]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "v" => (fun h:ℝ=>F (exteriorWave c h 0))

private theorem input_physical (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    v h∈evenBurnolClosedFace q := by
  have actual:=burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nn bound 0)
  obtain ⟨wave,inPa,same⟩:=Submodule.mem_map.mp actual
  change (wave:BurnolL2)=v h at same
  rw [←same]
  exact wave.property

/-- Exact original order qualifies the same actual B-wave action at every admitted source shift. -/
theorem original_B_forward_physical (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    R c (v h)∈evenBurnolClosedFace q := by
  obtain ⟨wave,inPa,same⟩:=Submodule.mem_map.mp (exterior_wave_inPa c h nn bound 0)
  change (wave:BurnolL2)=exteriorWave c h 0 at same
  have FourierPa:=burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa
  have physical:=CombSource.Division.whole_pa_physical observation nontrivial half.down 1
    (generatedRiemannXiZeroOrder_pos observation nontrivial)
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius wave) FourierPa
  change R c (F (wave:BurnolL2))∈evenBurnolClosedFace q at physical
  rwa [same] at physical

/-- Both B feet and the complete next programmes read the same qualified R occurrence. -/
theorem original_projection (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    gapSecondNext c (v h)=0 ∧
    firstNext (barC c) (F (v h))=0 ∧ secondNext (barC c) (F (v h))=0 := by
  have qualified:=input_physical observation nontrivial half h nn bound
  have even:reflectL2 (v h)=v h:=mem_evenL2ClosedFace_iff.mp qualified.2
  have physical:=physical_fibres ⟨R c (v h),original_B_forward_physical observation nontrivial half h nn bound⟩
  have gap:=actual_forward_R_gap_B c (v h) even qualified.1.1
  have full:=actual_forward_R_B c (v h) even
  exact ⟨gap.2.symm.trans physical.2,full.2.symm.trans physical.2,full.1.symm.trans physical.1⟩

/-- The unabridged first face retains the Fourier drive as well as the six-contact source action. -/
theorem original_full_source_equation (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    centeredQuarterStep (barC c) (b (F (v h)))+
      (-2*(sourceTail (barC c) (F (v h))+
        mu (Rq (F (v h)))*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))) • logBFirst (barC c) 0-
      BI (∑ i:Fin 6,contactCoefficients (barC c) (b (F (v h)):Hq) i • contactColumns (barC c) i)+
      BI (backwardContact (barC c) (Y (F (v h))))=0 := by
  simpa only [firstNext,currentAmplitude,contactAction] using
    (original_projection observation nontrivial half h nn bound).2.1

/-- This exposes the original mean, tail and all six fixed contacts before any further projection. -/
theorem original_gap_source_equation (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    centeredQuarterStep (barC c) (d (v h))+
      (-2*(sourceTail (barC c) (F (v h))+
        mu (Rq (F (v h)))*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))) • logBFirst (barC c) 0-
      BI (∑ i:Fin 6,contactCoefficients (barC c) (d (v h):Hq) i • contactColumns (barC c) i)=0 := by
  simpa only [gapSecondNext,currentAmplitude,contactAction] using
    (original_projection observation nontrivial half h nn bound).1

local notation "h0" => Real.log stageZeroSonineQ
theorem original_fixed_projection :
    gapSecondNext c (v h0)=0 ∧
    firstNext (barC c) (F (v h0))=0 ∧ secondNext (barC c) (F (v h0))=0 :=
  original_projection observation nontrivial half h0
    (Real.log_nonneg (by norm_num [stageZeroSonineQ]))
    ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small)

end OriginalBForwardGapProjectionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
