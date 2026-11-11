import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSBReverseCompactSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalKFiniteOrderRelease OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open private gamma
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private source_raw source_raw_tail
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactSource

open private pair_raw box_price
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private endpointColumn endpoint_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.NextEndpointProgramme
open private correction_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.EtaNextSourcePrice
open private coefficient
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer

def compactPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (kernel:ℝ→ℂ) : ℂ :=
  ∫ x:ℝ in symmetricInterval (q*Real.exp h),star (kernel x)*sourceRaw c h x

/-- The entire SB source price has finite support; the original complete B unit tail remains. -/
def lossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  compactPrice c h (OriginalNextEndpointProgramme.endpointRaw i)-
    centeringMean c h 0*tailPrice (OriginalNextEndpointProgramme.reciprocalEndpointRaw i) (unitCurrentProfile c)
def currentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  (2*gamma c)*OriginalNextEndpointProgramme.boundaryPrice c h i (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*OriginalNextEndpointProgramme.boundaryPrice c h i (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*lossPrice c h i
def correctionLossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  compactPrice c h (OriginalEtaNextSource.correctionRaw c)-
    centeringMean c h 0*tailPrice (OriginalEtaNextSource.reciprocalCorrectionRaw c) (unitCurrentProfile c)
def correctionCurrentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (2*gamma c)*OriginalEtaNextSource.correctionBoundaryPrice c h (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*OriginalEtaNextSource.correctionBoundaryPrice c h (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*correctionLossPrice c h

def programmePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  let a:=coefficient c
  let mean0:=OriginalCoreUnitProgramme.currentUnitPrice c h 0
  let mean1:=OriginalCoreUnitProgramme.currentUnitPrice c h 1
  let meanCore:=OriginalCoreUnitProgramme.coreUnitPrice c h 0
  (-star (Kernel.A c)*(currentPrice c h 0+(1-c.value)*mean0)-
    star (Kernel.beta c)*(currentPrice c h 1+c.value*mean1)+
    (c.value*star (gamma c)*mean0+2*a*star (gamma c)*meanCore-
      2*a*OriginalEtaNextSource.primitiveInputPrice c h-(2*c.value-1)*correctionCurrentPrice c h)-
    2*a*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+
    2*a*OriginalEtaNextSource.countedDifferencePrice c h)/(2*a)

private theorem compact_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (kernel:BurnolL2) (raw:ℝ→ℂ) (actual:(kernel:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ kernel (sourceField c zero h)=compactPrice c h raw := by
  rw [pair_raw _ _ _ _ actual (source_raw c zero h)]
  unfold rawPair compactPrice
  rw [←integral_indicator (measurableSet_symmetricInterval _)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases inside:x∈symmetricInterval (q*Real.exp h)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,source_raw_tail c h nn x
      (lt_of_not_ge (fun small=>inside (abs_le.mp small))),mul_zero]

/-- The actual full SB box and its centering unit are consumed together, by any same-source cotest. -/
theorem source_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (kernel:BurnolL2) (raw:ℝ→ℂ) (actual:(kernel:ℝ→ℂ)=ᵐ[volume] raw) :
    boxPrice raw q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrentProfile c)+
      centeringMean c h 1*rawPair raw (unitCurrentProfile c)=compactPrice c h raw := by
  have read:inner ℂ kernel (sourceField c zero h)=
      boxPrice raw q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrentProfile c)+
        centeringMean c h 1*rawPair raw (unitCurrentProfile c) := by
    unfold sourceField
    rw [inner_add_right,inner_smul_right,
      box_price _ _ _ _ actual (unitCurrent_raw c zero) _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
      pair_raw _ _ _ _ actual (unitCurrent_raw c zero)]
  exact read.symm.trans (compact_price c zero h nn kernel raw actual)

theorem loss_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (i:Fin 2) :
    OriginalBForwardEndpointSource.lossPrice c h i (unitCurrentProfile c)=lossPrice c h i := by
  unfold OriginalBForwardEndpointSource.lossPrice lossPrice
  rw [source_price c zero h nn (endpointColumn i) _ (endpoint_raw i)]
theorem current_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (i:Fin 2) :
    OriginalBForwardEndpointSource.currentPrice c h i=currentPrice c h i := by
  unfold OriginalBForwardEndpointSource.currentPrice currentPrice
  rw [loss_price c zero h nn i]
theorem correction_current_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    OriginalBForwardEndpointSource.correctionCurrentPrice c h=correctionCurrentPrice c h := by
  unfold OriginalBForwardEndpointSource.correctionCurrentPrice correctionCurrentPrice
  unfold OriginalBForwardEndpointSource.correctionLossPrice correctionLossPrice
  rw [source_price c zero h nn (OriginalRieszSourceGreen.sourceCorrection c) _ (correction_raw c)]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ
/-- All three original SB prices now consume the source-generated compact field at the original c/h. -/
theorem original_programmePrice :
    OriginalBForwardEndpointSource.programmePrice c h0=programmePrice c h0 := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  unfold OriginalBForwardEndpointSource.programmePrice programmePrice
  dsimp only
  rw [current_price c observation.mathlibZero h0 nn 0,current_price c observation.mathlibZero h0 nn 1,
    correction_current_price c observation.mathlibZero h0 nn]
theorem original_fixedResidual_programme :
    burnolPaFixedShiftResidual c observation.mathlibZero=programmePrice c h0 :=
  (OriginalBForwardEndpointSource.original_fixedResidual_programme observation nontrivial half).trans
    (original_programmePrice observation nontrivial half)

end OriginalSBReverseCompactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
