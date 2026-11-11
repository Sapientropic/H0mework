import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CoreComparison
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalReverseCoreBalanceConsumer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKFixedBoundarySourceFibre
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction
open OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "TD" => TemperedDistribution ℝ ℂ

private theorem inverse_regular_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (i:Fin 2) :
    2*inner ℂ (regularColumns c i) value=
      inner ℂ (regularForcing c i) (R c value)-
        (2*c.value-1)*inner ℂ (regularColumns c i) (R c value) := by
  have left:=regularColumns_euler c i
  have right : GapEuler.euler (R c value:TD)+(c.value-1/2) • (R c value:TD)=
      (-2:ℂ) • (value:TD) := by
    change GapEuler.euler (burnolDirectRightResolvent (c.value/2) value:TD)+
      (c.value-1/2) • (burnolDirectRightResolvent (c.value/2) value:TD)=(-2:ℂ) • (value:TD)
    simpa only [sourceResolvent,sourceRate,
      OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
      using sourceResolvent_euler (barC c) value
  have leftActual : GapEuler.euler (regularColumns c i:TD)=
      (regularForcing c i-sourceRate c • regularColumns c i:BurnolL2) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq left
  have rightActual : GapEuler.euler (R c value:TD)=
      ((-2:ℂ) • value-(c.value-1/2) • R c value:BurnolL2) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq right
  have actual:=DilationWard.cross_balance (regularColumns c i)
    (regularForcing c i-sourceRate c • regularColumns c i) (R c value)
    ((-2:ℂ) • value-(c.value-1/2) • R c value) leftActual rightActual
  unfold sourceRate at actual
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    star_sub,star_div₀,star_one,star_ofNat,star_star,starRingEnd_apply] at actual
  linear_combination -actual

theorem inverse_original_K_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    2*inner ℂ (sourceKernel c) value=
      star (Kernel.A c)*inner ℂ (regularForcing c 0) (R c value)+
      star (Kernel.beta c)*inner ℂ (regularForcing c 1) (R c value)-
      (2*c.value-1)*inner ℂ (sourceKernel c) (R c value)+
      2*inner ℂ (wholeJump c) value+(2*c.value-1)*inner ℂ (wholeJump c) (R c value) := by
  have source : sourceKernel c=
      Kernel.A c • (regularColumns c 0+jumpColumns 0)+
      Kernel.beta c • (regularColumns c 1+jumpColumns 1) := by
    have generated : generatedK c=∑ i:Fin 2,sourceCoefficients c i • sourceColumns c i := by
      simp only [generatedK,Fin.sum_univ_two,sourceCoefficients,sourceColumns,
        Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [sourceKernel_original,←generatedK_eq_original,generated]
    simp only [Fin.sum_univ_two,sourceCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one,
      sourceColumns_from_regular_resolvent]
  rw [source]
  simp only [wholeJump,Fin.sum_univ_two,sourceCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one,
    inner_add_left,inner_smul_left,starRingEnd_apply]
  linear_combination star (Kernel.A c)*(inverse_regular_price c value 0)+
    star (Kernel.beta c)*(inverse_regular_price c value 1)

open private gamma gamma_ne_zero difference_ne_zero reverseCoreRCurrent
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

/-- The actual reverse R programme is priced with the original jump and complete counted difference. -/
def fixedRPrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  let coefficient:=(c.value-star c.value)*gamma (barC c)
  let current:=reverseCoreRCurrent c zero h
  let difference:=coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
      inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h+
    (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantForward.value)-
      inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0)))
  (-star (Kernel.A c)*inner ℂ (regularForcing c 0) current-
    star (Kernel.beta c)*inner ℂ (regularForcing c 1) current+
    (2*c.value-1)*inner ℂ (sourceKernel c) current-
    2*coefficient*inner ℂ (wholeJump c) (coreReverseSource c zero h)-
    (2*c.value-1)*inner ℂ (wholeJump c) current+2*coefficient*difference)/(2*coefficient)

/-- This rewrites the original fixed residual, using the generated R effect of that same reverse core. -/
theorem original_fixedResidual_R_price (observation:GeneratedRiemannZeroObservation)
    (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half:OriginalKCombCalculation.Half observation) :
    let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    burnolPaFixedShiftResidual c observation.mathlibZero=
      fixedRPrice c observation.mathlibZero (Real.log stageZeroSonineQ) := by
  let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  let h:=Real.log stageZeroSonineQ
  let coefficient:=((c).value-star (c).value)*gamma (barC c)
  have nonzero:coefficient≠0:=mul_ne_zero (difference_ne_zero observation nontrivial half)
    (gamma_ne_zero (barC c))
  have nn:0≤h:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have bound:h≤Real.log 2:=(le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
  have ward:=original_core_arithmetic_ward c observation.mathlibZero h nn
  have comparison:=original_core_counted_difference c observation.mathlibZero h nn bound
  rw [ward] at comparison
  have residual:=original_fixedResidual_core c observation.mathlibZero h nn rfl
  have source:
      burnolPaFixedShiftResidual c observation.mathlibZero=
      -inner ℂ (sourceKernel c) (coreReverseSource c observation.mathlibZero h)+
        (coreCharacterDefect c h*(reverseMean c observation.mathlibZero*inner ℂ (sourceKernel c) ConstantDual.seed-
          inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h+
        (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantForward.value)-
          inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0)))) := by
    linear_combination residual+comparison
  have price:=inverse_original_K_price c (coreReverseSource c observation.mathlibZero h)
  have actual:=OriginalReverseSourceRTail.original_fixed_reverse_R_update observation nontrivial half
  change coefficient • R c (coreReverseSource c observation.mathlibZero h)=
    reverseCoreRCurrent c observation.mathlibZero h at actual
  change burnolPaFixedShiftResidual c observation.mathlibZero=fixedRPrice c observation.mathlibZero h
  unfold fixedRPrice
  dsimp only
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℂ)≠0) nonzero)).2
  rw [←actual]
  simp only [inner_smul_right]
  linear_combination (2*coefficient)*source-coefficient*price

end OriginalReverseCoreBalanceConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
