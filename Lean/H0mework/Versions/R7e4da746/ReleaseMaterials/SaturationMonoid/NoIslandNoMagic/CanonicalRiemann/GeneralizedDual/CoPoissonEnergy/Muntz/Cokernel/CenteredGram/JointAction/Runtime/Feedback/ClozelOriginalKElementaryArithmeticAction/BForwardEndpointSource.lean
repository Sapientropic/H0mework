import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.NextEndpointProgramme
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Source.Division.Whole

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBForwardEndpointSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalKFiniteOrderRelease OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "L" => OriginalRieszSourceGreen.sourceCorrection

open private gamma unitCurrent FT boxProgram boxProgram_actual boxProgram_R FT_R unitTailProgram
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private box_price unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private endpointColumn reciprocal_endpoint_raw FT_price
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.NextEndpointProgramme
open private physical_extension_zero physical_fourier_extension_zero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBFiniteAction.Source
open private coefficient
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer

private theorem physical_cotest (test:BurnolPaAmbientCarrier) (s t:M) :
    inner ℂ (F (E (s:Hq))-E (t:Hq)) (test:BurnolL2)=0 := by
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right,physical_fourier_extension_zero,physical_extension_zero,sub_self]

private theorem endpoint_physical (i:Fin 2) (test:BurnolPaAmbientCarrier) :
    inner ℂ (endpointColumn i) (test:BurnolL2)=0 := by
  fin_cases i
  · exact physical_cotest test Response.u Response.v
  · apply inner_eq_zero_symm.mp
    change inner ℂ (test:BurnolL2) (E (Response.u:Hq)-F (E (Response.v:Hq)))=0
    rw [inner_sub_right,physical_extension_zero,physical_fourier_extension_zero,sub_self]

private theorem wave_R_programme (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) :
    R c (F (exteriorWave c h 0))=FT (boxProgram (bandLower h) 4 (positiveWeight c h 0)
      (deriv (positiveWeight c h 0)) (unitCurrent c zero)) := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  have wave:T (exteriorWave c h 0)=boxProgram (bandLower h) 4 (positiveWeight c h 0)
      (deriv (positiveWeight c h 0)) ConstantDual.value :=
    boxProgram_actual _ _ _ _ (bandLower_pos h) regular
  have forward:F (exteriorWave c h 0)=FT (boxProgram (bandLower h) 4 (positiveWeight c h 0)
      (deriv (positiveWeight c h 0)) ConstantDual.value) := by
    rw [←wave]
    change F (exteriorWave c h 0)=F (T (T (exteriorWave c h 0)))
    rw [burnolTateReciprocalL2_involutive]
  rw [forward,←FT_R,boxProgram_R c _ _ _ _ (bandLower_pos h) regular,actual_unit_R]

/-- The original SB box, both actual means, and the complete B-unit tail remain. -/
def lossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) (raw:ℝ→ℂ) : ℂ :=
  boxPrice (OriginalNextEndpointProgramme.endpointRaw i) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) raw+
    centeringMean c h 1*rawPair (OriginalNextEndpointProgramme.endpointRaw i) raw-
    centeringMean c h 0*tailPrice (OriginalNextEndpointProgramme.reciprocalEndpointRaw i) raw

def currentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  (2*gamma c)*OriginalNextEndpointProgramme.boundaryPrice c h i (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*OriginalNextEndpointProgramme.boundaryPrice c h i (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*lossPrice c h i (unitCurrentProfile c)

def correctionLossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (raw:ℝ→ℂ) : ℂ :=
  boxPrice (OriginalEtaNextSource.correctionRaw c) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) raw+
    centeringMean c h 1*rawPair (OriginalEtaNextSource.correctionRaw c) raw-
    centeringMean c h 0*tailPrice (OriginalEtaNextSource.reciprocalCorrectionRaw c) raw

def correctionCurrentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (2*gamma c)*OriginalEtaNextSource.correctionBoundaryPrice c h (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*OriginalEtaNextSource.correctionBoundaryPrice c h (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*correctionLossPrice c h (unitCurrentProfile c)

/-- The same complete original programme consumes all three B-forward box effects. -/
def programmePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  let a:=coefficient c
  let mean0:=OriginalCoreUnitProgramme.currentUnitPrice c h 0
  let mean1:=OriginalCoreUnitProgramme.currentUnitPrice c h 1
  let meanCore:=OriginalCoreUnitProgramme.coreUnitPrice c h 0
  (-star (Kernel.A c)*(currentPrice c h 0+(1-c.value)*mean0)-
    star (Kernel.beta c)*(currentPrice c h 1+c.value*mean1)+
    (c.value*star (gamma c)*mean0+2*a*star (gamma c)*meanCore-
      2*a*OriginalEtaNextSource.primitiveInputPrice c h-
      (2*c.value-1)*correctionCurrentPrice c h)-
    2*a*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+
    2*a*OriginalEtaNextSource.countedDifferencePrice c h)/(2*a)

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ

/-- Exact original order supplies the physical qualification of the actual B-wave R action. -/
theorem original_B_forward_physical :
    R c (F (exteriorWave c h0 0))∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have bounded:h0≤Real.log 2:=
    (le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
  obtain ⟨wave,inPa,same⟩:=Submodule.mem_map.mp (exterior_wave_inPa c h0 nn bounded 0)
  change (wave:BurnolL2)=exteriorWave c h0 0 at same
  have FourierPa:=burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa
  have physical:=CombSource.Division.whole_pa_physical observation nontrivial half.down 1
    (generatedRiemannXiZeroOrder_pos observation nontrivial)
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius wave) FourierPa
  change R c (F (wave:BurnolL2))∈evenBurnolClosedFace burnolUnscaledCommonGapRadius at physical
  rwa [same] at physical

private def BForward : BurnolPaAmbientCarrier :=
  ⟨R c (F (exteriorWave c h0 0)),original_B_forward_physical observation nontrivial half⟩

/-- Both original full B-forward endpoints retain precisely their complete original unit price. -/
theorem original_full_B_forward_endpoint (i:Fin 2) :
    inner ℂ (endpointColumn i) (R c (F (FullUnit.fullForward c h0 0)))=
      centeringMean c h0 0*inner ℂ (endpointColumn i) (R c (F ConstantForward.value)) := by
  change inner ℂ (endpointColumn i) (R c (F (exteriorWave c h0 0+
    centeringMean c h0 0 • ConstantForward.value)))=_
  rw [map_add,map_smul,map_add,map_smul,inner_add_right,inner_smul_right]
  have paid:=endpoint_physical i (BForward observation nontrivial half)
  change inner ℂ (endpointColumn i) (R c (F (exteriorWave c h0 0)))=0 at paid
  rw [paid,zero_add]

/-- The whole actual B box in each original endpoint programme is paid by that same action. -/
theorem original_B_box (i:Fin 2) :
    boxPrice (OriginalNextEndpointProgramme.reciprocalEndpointRaw i) (bandLower h0) 4
      (positiveWeight c h0 0) (deriv (positiveWeight c h0 0)) (unitCurrentProfile c)=0 := by
  have regular:ContinuousOn (deriv (positiveWeight c h0 0)) (Icc (bandLower h0) 4) :=
    (positiveWeight_deriv_continuousOn c h0 0).mono (fun _ inside=>(bandLower_pos h0).trans_le inside.1)
  have read:inner ℂ (endpointColumn i) (R c (F (exteriorWave c h0 0)))=
      boxPrice (OriginalNextEndpointProgramme.reciprocalEndpointRaw i) (bandLower h0) 4
        (positiveWeight c h0 0) (deriv (positiveWeight c h0 0)) (unitCurrentProfile c) := by
    rw [wave_R_programme c observation.mathlibZero h0,FT_price]
    exact box_price _ _ _ _ (reciprocal_endpoint_raw i) (unitCurrent_raw c observation.mathlibZero)
      _ _ _ _ (bandLower_pos h0) regular
  exact read.symm.trans (endpoint_physical i (BForward observation nontrivial half))

theorem original_lossPrice (i:Fin 2) :
    OriginalNextEndpointProgramme.lossPrice c h0 i (unitCurrentProfile c)=
      lossPrice c h0 i (unitCurrentProfile c) := by
  unfold OriginalNextEndpointProgramme.lossPrice lossPrice
  rw [original_B_box observation nontrivial half i,zero_add]

theorem original_currentPrice (i:Fin 2) :
    OriginalNextEndpointProgramme.currentPrice c h0 i=currentPrice c h0 i := by
  unfold OriginalNextEndpointProgramme.currentPrice currentPrice
  rw [original_lossPrice observation nontrivial half i]

namespace Correction
open private reciprocal_correction_raw FT_price
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.EtaNextSourcePrice

/-- The same actual physical output pays the original B-correction cotest as well. -/
theorem original_B_box :
    boxPrice (OriginalEtaNextSource.reciprocalCorrectionRaw c) (bandLower h0) 4
      (positiveWeight c h0 0) (deriv (positiveWeight c h0 0)) (unitCurrentProfile c)=0 := by
  have regular:ContinuousOn (deriv (positiveWeight c h0 0)) (Icc (bandLower h0) 4) :=
    (positiveWeight_deriv_continuousOn c h0 0).mono (fun _ inside=>(bandLower_pos h0).trans_le inside.1)
  have read:inner ℂ (L c) (R c (F (exteriorWave c h0 0)))=
      boxPrice (OriginalEtaNextSource.reciprocalCorrectionRaw c) (bandLower h0) 4
        (positiveWeight c h0 0) (deriv (positiveWeight c h0 0)) (unitCurrentProfile c) := by
    rw [wave_R_programme c observation.mathlibZero h0,FT_price c]
    exact box_price _ _ _ _ (reciprocal_correction_raw c) (unitCurrent_raw c observation.mathlibZero)
      _ _ _ _ (bandLower_pos h0) regular
  exact read.symm.trans (physical_cotest (BForward observation nontrivial half) (sourceB c) (sourceSB c))
end Correction

theorem original_correctionLossPrice :
    OriginalEtaNextSource.correctionLossPrice c h0 (unitCurrentProfile c)=
      correctionLossPrice c h0 (unitCurrentProfile c) := by
  unfold OriginalEtaNextSource.correctionLossPrice correctionLossPrice
  rw [Correction.original_B_box observation nontrivial half,zero_add]

theorem original_correctionCurrentPrice :
    OriginalEtaNextSource.correctionCurrentPrice c h0=correctionCurrentPrice c h0 := by
  unfold OriginalEtaNextSource.correctionCurrentPrice correctionCurrentPrice
  rw [original_correctionLossPrice observation nontrivial half]

/-- All original B-forward box terms are consumed inside the complete same-c/h programme. -/
theorem original_programmePrice :
    OriginalNextEndpointProgramme.programmePrice c h0=programmePrice c h0 := by
  unfold OriginalNextEndpointProgramme.programmePrice programmePrice
  dsimp only
  rw [original_currentPrice observation nontrivial half 0,original_currentPrice observation nontrivial half 1,
    original_correctionCurrentPrice observation nontrivial half]

/-- The original fixed residual reads the programme after its actual B-forward effects are paid. -/
theorem original_fixedResidual_programme :
    burnolPaFixedShiftResidual c observation.mathlibZero=programmePrice c h0 :=
  (OriginalNextEndpointProgramme.original_fixedResidual_programme observation nontrivial half).trans
    (original_programmePrice observation nontrivial half)

end OriginalBForwardEndpointSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
