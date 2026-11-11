import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CorePrimitiveSourcePrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteCountedSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCurrentRegularPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction OriginalKFiniteOrderRelease
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "P" => Constructor.zeroMean
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private extension_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private cutMap cut_reflection
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CorePosition
open private dual_reflect
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy

private theorem core_source_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    reflectL2 (sourceCore c h)=sourceCore c h := by
  have evenE:reflectL2 (elementarySource c)=elementarySource c := burnolAmbientEvenPart_even _
  have evenB:reflectL2 (E (sourceB c:Hq))=E (sourceB c:Hq) :=
    extension_even _ (burnolRieszSingleFourierSource_reflection_fixed c)
  have evenC:reflectL2 ConstantDual.seed=ConstantDual.seed :=
    extension_even _ (reflectRestricted_intervalConstant q)
  have evenLoss:reflectL2 (FullUnit.fullSource c h 0)=FullUnit.fullSource c h 0 := by
    change reflectL2 (burnolMultiplicativeDilation (-h) (E (sourceB c:Hq))-
      cutMap q (burnolMultiplicativeDilation (-h) (E (sourceB c:Hq)))+
        OriginalKSourceFiniteUpdate.OriginalBFiniteAction.outwardMean h (sourceB c) • ConstantDual.seed)=_
    rw [map_add,map_sub,map_smul,cut_reflection,reflectL2_burnolMultiplicativeDilation,evenB,evenC]
    rfl
  rw [core_two_foot_source,map_add,map_add,map_smul,map_smul,evenE,position_core_even,
    ←fourierL2_reflectL2_commute,evenLoss]

private theorem core_reverse_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) : reflectL2 (coreReverseSource c zero h)=coreReverseSource c zero h := by
  have source:=core_reverse_tendsto c zero h nn
  have returned:=(reflectL2.continuous.tendsto _).comp source
  have same:(fun N:ℕ=>reflectL2 (DualSource.source N (sourceCore c h)))=
      (fun N:ℕ=>DualSource.source N (sourceCore c h)) := by
    funext N
    rw [dual_reflect,core_source_even]
  change Tendsto (fun N:ℕ=>reflectL2 (DualSource.source N (sourceCore c h))) atTop
    (𝓝 (reflectL2 (coreReverseSource c zero h))) at returned
  rw [same] at returned
  exact tendsto_nhds_unique returned source

open private gamma
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
private def coefficient (c:BurnolCompletedMellinCoordinate) : ℂ :=
  (c.value-star c.value)*gamma (OriginalPrimitiveRankBalance.conjugateCoordinate c)
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ
local notation "a" => coefficient c
local notation "v" => coreReverseSource c observation.mathlibZero h0
local notation "current" => OriginalFullLossRAction.completeCoreRCurrent c observation.mathlibZero h0
local notation "nextFirst" => GenericSourceStepBAction.firstNext
  (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 v)
local notation "nextSecond" => GenericSourceStepBAction.secondNext
  (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 v)

/-- Complete current prices consume actual B update, Euler and the calculated input programme. -/
theorem original_current_prices :
    inner ℂ (regularForcing c 0) current=
      a*(q:ℂ)*(burnolMeanZeroFourierRaw nextFirst q+burnolMeanZeroFourierRaw nextFirst (-q))+
        (1-(c).value)*inner ℂ ConstantDual.seed current ∧
    inner ℂ (regularForcing c 1) current=
      a*(q:ℂ)*(burnolMeanZeroFourierRaw nextSecond q+burnolMeanZeroFourierRaw nextSecond (-q))+
        (c).value*inner ℂ (fourierL2 ConstantDual.seed) current ∧
    (2*(c).value-1)*inner ℂ (sourceKernel c) current=
      (c).value*star (gamma c)*inner ℂ ConstantDual.seed current+
        2*a*star (gamma c)*inner ℂ ConstantDual.seed v-
        2*a*elementaryCoreSourcePrice c h0-
        (2*(c).value-1)*a*inner ℂ (sourceEta c) nextFirst := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have bound:h0≤Real.log 2:=(le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
  have even:=core_reverse_even c observation.mathlibZero h0 nn
  have prices:=actual_regular_R_prices c v even
  have Kprice:=actual_original_K_R_price c v even
  have primitive:=elementary_R_action c v
  have calculated:=elementary_core_source c observation.mathlibZero h0 nn bound
  rw [calculated] at primitive
  have source:=OriginalFullLossRAction.original_core_R_update observation nontrivial half
  change a • burnolDirectRightResolventCLM c v=current at source
  rw [←source]
  simp only [inner_smul_right]
  refine ⟨?_,?_,?_⟩
  · rw [prices.1]
    ring
  · rw [prices.2]
    ring
  · rw [Kprice]
    change (2*(c).value-1)*(a*(inner ℂ (elementarySource c) (burnolDirectRightResolventCLM c v)-
      inner ℂ (sourceEta c) nextFirst))=_
    change (2*(c).value-1)*inner ℂ (elementarySource c) (burnolDirectRightResolventCLM c v)=
      (c).value*star (gamma c)*inner ℂ ConstantDual.seed (burnolDirectRightResolventCLM c v)+
        2*star (gamma c)*inner ℂ ConstantDual.seed v-2*elementaryCoreSourcePrice c h0 at primitive
    linear_combination a*primitive

/-- The original fixed residual consumes the entire calculated regular, original-K and jump prices. -/
theorem original_fixedResidual_source_prices :
    burnolPaFixedShiftResidual c observation.mathlibZero=
      (-star (Kernel.A c)*(a*(q:ℂ)*(burnolMeanZeroFourierRaw nextFirst q+
          burnolMeanZeroFourierRaw nextFirst (-q))+(1-(c).value)*inner ℂ ConstantDual.seed current)-
        star (Kernel.beta c)*(a*(q:ℂ)*(burnolMeanZeroFourierRaw nextSecond q+
          burnolMeanZeroFourierRaw nextSecond (-q))+(c).value*inner ℂ (fourierL2 ConstantDual.seed) current)+
        ((c).value*star (gamma c)*inner ℂ ConstantDual.seed current+
          2*a*star (gamma c)*inner ℂ ConstantDual.seed v-2*a*elementaryCoreSourcePrice c h0-
          (2*(c).value-1)*a*inner ℂ (sourceEta c) nextFirst)-
        2*a*OriginalReverseCoreJumpMean.coreJumpPrice c h0-
        (2*(c).value-1)*OriginalReverseCoreJumpMean.currentJumpPrice c h0+
        2*a*OriginalCompleteCountedSource.calculatedDifference c h0)/(2*a) := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have read:=OriginalReverseCoreJumpMean.original_fixedResidual_jump_programme observation nontrivial half
  change burnolPaFixedShiftResidual c observation.mathlibZero=
    OriginalReverseCoreJumpMean.fixedJumpProgrammePrice c observation.mathlibZero h0 at read
  rw [OriginalCompleteCountedSource.fixed_price_source c observation.mathlibZero h0 nn] at read
  change burnolPaFixedShiftResidual c observation.mathlibZero=
    (-star (Kernel.A c)*inner ℂ (regularForcing c 0) current-
      star (Kernel.beta c)*inner ℂ (regularForcing c 1) current+
      (2*(c).value-1)*inner ℂ (sourceKernel c) current-
      2*a*OriginalReverseCoreJumpMean.coreJumpPrice c h0-
      (2*(c).value-1)*OriginalReverseCoreJumpMean.currentJumpPrice c h0+
      2*a*OriginalCompleteCountedSource.calculatedDifference c h0)/(2*a) at read
  rw [(original_current_prices observation nontrivial half).1,
    (original_current_prices observation nontrivial half).2.1,
    (original_current_prices observation nontrivial half).2.2] at read
  exact read

end OriginalCurrentRegularPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
