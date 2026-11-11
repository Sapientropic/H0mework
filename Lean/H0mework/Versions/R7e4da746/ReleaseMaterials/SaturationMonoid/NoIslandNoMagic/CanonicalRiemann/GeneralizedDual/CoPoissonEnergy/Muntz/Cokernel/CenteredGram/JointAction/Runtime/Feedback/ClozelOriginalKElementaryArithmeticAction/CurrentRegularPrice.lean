import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreBalanceConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price
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
open private inner_evenPart extension_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private position_fourier
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private qualified_S_pairing_left
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price

private theorem extension_price (state:M) (even:reflectRestricted q (state:Hq)=state) (value:BurnolL2) :
    inner ℂ (E (state:Hq)) value=inner ℂ state (X value) := by
  rw [←inner_evenPart (E (state:Hq)) value (extension_even _ even)]
  change inner ℂ (E (state:Hq)) (burnolAmbientEvenPart value)=
    inner ℂ (state:Hq) (P (Rq (burnolAmbientEvenPart value)):Hq)
  have adjacent:=ContinuousLinearMap.adjoint_inner_left Rq (burnolAmbientEvenPart value) (state:Hq)
  change inner ℂ (E (state:Hq)) (burnolAmbientEvenPart value)=inner ℂ (state:Hq) (Rq (burnolAmbientEvenPart value)) at adjacent
  rw [adjacent]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left state _).symm

private theorem fourier_extension_price (state:M) (even:reflectRestricted q (state:Hq)=state) (value:BurnolL2) :
    inner ℂ (fourierL2 (E (state:Hq))) value=inner ℂ state (Y value) := by
  have paired:=fourierL2.inner_map_map (fourierL2 (E (state:Hq))) value
  rw [fourierL2_fourierL2,extension_even _ even] at paired
  rw [←paired,extension_price state even,position_fourier]

private theorem response_prices (value:BurnolL2) :
    inner ℂ Response.u (Y value)-inner ℂ Response.v (X value)=inner ℂ Response.eta (d value) ∧
    inner ℂ Response.u (X value)-inner ℂ Response.v (Y value)=inner ℂ Response.eta (b value) := by
  have first:=burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  have second:=burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs value)
  change b value+S (d value)=X value at first
  change S (b value)+d value=Y value at second
  have uPair (t:M) : inner ℂ Response.u (S t)=inner ℂ Response.v t :=
    qualified_S_pairing_left Response.u t Response.u_reflection
  have vPair (t:M) : inner ℂ Response.v (S t)=inner ℂ (S Response.v) t :=
    qualified_S_pairing_left Response.v t Response.v_reflection
  have native:Response.u-S Response.v=Response.eta := Response.source_pair_equation
  rw [←first,←second,←native]
  simp only [inner_add_right,inner_sub_left,uPair,vPair]
  constructor <;> ring

private theorem original_B_pair (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (sourceSB c) (X value)-inner ℂ (sourceB c) (Y value)=
      -inner ℂ (sourceEta c) (d value) := by
  have first:=burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  have second:=burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs value)
  change b value+S (d value)=X value at first
  change S (b value)+d value=Y value at second
  have BParity:reflectRestricted q (sourceB c:Hq)=sourceB c := burnolRieszSingleFourierSource_reflection_fixed c
  have sourceParity:sourceMeanZeroReflection (sourceB c)=sourceB c := Subtype.ext BParity
  have returned:=sourceMeanZeroFourier_reflect (sourceB c)
  rw [sourceParity] at returned
  have SBParity:reflectRestricted q (sourceSB c:Hq)=sourceSB c :=
    congrArg (fun v:M=>(v:Hq)) returned.symm
  have firstPair (t:M) : inner ℂ (sourceB c) (S t)=inner ℂ (sourceSB c) t :=
    qualified_S_pairing_left _ _ BParity
  have secondPair (t:M) : inner ℂ (sourceSB c) (S t)=inner ℂ (S (sourceSB c)) t :=
    qualified_S_pairing_left _ _ SBParity
  have native:sourceB c-S (sourceSB c)=sourceEta c := source_pair_equation c
  rw [←first,←second,←native]
  simp only [inner_add_right,inner_sub_left,firstPair,secondPair]
  ring

/-- Original u/v source equations pay the full regular forcing by actual B boundary legs and both units. -/
theorem regular_prices (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (regularForcing c 0) value=inner ℂ Response.eta (d value)+
      (1-c.value)*inner ℂ ConstantDual.seed value ∧
    inner ℂ (regularForcing c 1) value=inner ℂ Response.eta (b value)+
      c.value*inner ℂ (fourierL2 ConstantDual.seed) value := by
  have pair:=response_prices value
  constructor
  · simp only [regularForcing,Matrix.cons_val_zero,inner_add_left,inner_sub_left,inner_smul_left]
    change inner ℂ (fourierL2 (E (Response.u:Hq))) value-inner ℂ (E (Response.v:Hq)) value+
      star (1/2-sourceRate c)*inner ℂ ConstantDual.seed value=_
    rw [fourier_extension_price _ Response.u_reflection,extension_price _ Response.v_reflection]
    rw [show inner ℂ Response.u (Y value)-inner ℂ Response.v (X value)=inner ℂ Response.eta (d value) from pair.1]
    unfold sourceRate
    simp only [star_sub,star_div₀,star_one,star_ofNat,star_star]
    ring
  · simp only [regularForcing,Matrix.cons_val_one,Matrix.cons_val_zero,inner_add_left,inner_sub_left,inner_smul_left]
    change inner ℂ (E (Response.u:Hq)) value-inner ℂ (fourierL2 (E (Response.v:Hq))) value+
      star (sourceRate c+1/2)*inner ℂ (fourierL2 ConstantDual.seed) value=_
    rw [extension_price _ Response.u_reflection,fourier_extension_price _ Response.v_reflection]
    rw [show inner ℂ Response.u (X value)-inner ℂ Response.v (Y value)=inner ℂ Response.eta (b value) from pair.2]
    unfold sourceRate
    simp only [star_add,star_sub,star_div₀,star_one,star_ofNat,star_star]
    ring

/-- The original source B equation removes the complete physical K correction from its actual cotest. -/
theorem original_K_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (sourceKernel c) value=inner ℂ (elementarySource c) value-
      inner ℂ (sourceEta c) (d value) := by
  have BParity:reflectRestricted q (sourceB c:Hq)=sourceB c := burnolRieszSingleFourierSource_reflection_fixed c
  have sourceParity:sourceMeanZeroReflection (sourceB c)=sourceB c := Subtype.ext BParity
  have returned:=sourceMeanZeroFourier_reflect (sourceB c)
  rw [sourceParity] at returned
  have SBParity:reflectRestricted q (sourceSB c:Hq)=sourceSB c :=
    congrArg (fun v:M=>(v:Hq)) returned.symm
  unfold sourceKernel
  rw [inner_sub_left,inner_add_left,extension_price _ SBParity,fourier_extension_price _ BParity]
  linear_combination original_B_pair c value

/-- The actual source R/B update now pays the two nonunit forcing prices at actual endpoints. -/
theorem actual_regular_R_prices (c:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (even:reflectL2 value=value) :
    inner ℂ (regularForcing c 0) (burnolDirectRightResolventCLM c value)=
      (q:ℂ)*(burnolMeanZeroFourierRaw (GenericSourceStepBAction.firstNext
        (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 value)) q+
        burnolMeanZeroFourierRaw (GenericSourceStepBAction.firstNext
          (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 value)) (-q))+
        (1-c.value)*inner ℂ ConstantDual.seed (burnolDirectRightResolventCLM c value) ∧
    inner ℂ (regularForcing c 1) (burnolDirectRightResolventCLM c value)=
      (q:ℂ)*(burnolMeanZeroFourierRaw (GenericSourceStepBAction.secondNext
        (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 value)) q+
        burnolMeanZeroFourierRaw (GenericSourceStepBAction.secondNext
          (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 value)) (-q))+
        c.value*inner ℂ (fourierL2 ConstantDual.seed) (burnolDirectRightResolventCLM c value) := by
  have source:=GenericSourceStepBAction.actual_forward_R_B c value even
  have prices:=regular_prices c (burnolDirectRightResolventCLM c value)
  rw [source.2,source.1,OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read,
    OriginalCommonInverseForcing.InverseEuler.eta_endpoint_read] at prices
  exact prices

/-- Its K price uses the same generated first-next B leg and the original elementary source. -/
theorem actual_original_K_R_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (even:reflectL2 value=value) :
    inner ℂ (sourceKernel c) (burnolDirectRightResolventCLM c value)=
      inner ℂ (elementarySource c) (burnolDirectRightResolventCLM c value)-
        inner ℂ (sourceEta c) (GenericSourceStepBAction.firstNext
          (OriginalPrimitiveRankBalance.conjugateCoordinate c) (fourierL2 value)) := by
  rw [original_K_price,(GenericSourceStepBAction.actual_forward_R_B c value even).2]

/-- Actual cross-Euler balance pays the elementary source R price by its input and complete unit. -/
theorem elementary_R_action (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    (2*c.value-1)*inner ℂ (elementarySource c) (burnolDirectRightResolventCLM c value)=
      c.value*star (star c.value*GapEuler.gapMean q c)*
          inner ℂ ConstantDual.seed (burnolDirectRightResolventCLM c value)+
        2*star (star c.value*GapEuler.gapMean q c)*inner ℂ ConstantDual.seed value-
        2*inner ℂ (elementarySource c) value := by
  let left:=sourceResolvent c ConstantDual.seed
  let right:=burnolDirectRightResolventCLM c value
  have leftEuler:=sourceResolvent_euler c ConstantDual.seed
  have rightEuler:=sourceResolvent_euler (OriginalPrimitiveRankBalance.conjugateCoordinate c) value
  simp only [sourceResolvent,sourceRate,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at rightEuler
  change GapEuler.euler (left:TemperedDistribution ℝ ℂ)+
    sourceRate c • (left:TemperedDistribution ℝ ℂ)=(-2:ℂ) • (ConstantDual.seed:TemperedDistribution ℝ ℂ) at leftEuler
  change GapEuler.euler (right:TemperedDistribution ℝ ℂ)+
    (c.value-1/2) • (right:TemperedDistribution ℝ ℂ)=(-2:ℂ) • (value:TemperedDistribution ℝ ℂ) at rightEuler
  have leftActual:GapEuler.euler (left:TemperedDistribution ℝ ℂ)=
      ((-2:ℂ) • ConstantDual.seed-sourceRate c • left:BurnolL2) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq leftEuler
  have rightActual:GapEuler.euler (right:TemperedDistribution ℝ ℂ)=
      ((-2:ℂ) • value-(c.value-1/2) • right:BurnolL2) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq rightEuler
  have actual:=DilationWard.cross_balance left
    ((-2:ℂ) • ConstantDual.seed-sourceRate c • left) right
    ((-2:ℂ) • value-(c.value-1/2) • right) leftActual rightActual
  unfold sourceRate at actual
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    star_sub,star_neg,star_div₀,star_one,star_ofNat,star_star,starRingEnd_apply] at actual
  rw [←elementary_unit_resolvent c]
  simp only [unitResolventSource,inner_smul_left,inner_sub_left,star_sub,
    star_div₀,star_one,star_ofNat,star_star,starRingEnd_apply]
  change (2*c.value-1)*(star (star c.value*GapEuler.gapMean q c)*
      (inner ℂ ConstantDual.seed right-((1-c.value)/2)*inner ℂ left right))=_
  dsimp only [left,right] at actual ⊢
  linear_combination ((1-c.value)/2*star (star c.value*GapEuler.gapMean q c))*actual

end OriginalCurrentRegularPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
