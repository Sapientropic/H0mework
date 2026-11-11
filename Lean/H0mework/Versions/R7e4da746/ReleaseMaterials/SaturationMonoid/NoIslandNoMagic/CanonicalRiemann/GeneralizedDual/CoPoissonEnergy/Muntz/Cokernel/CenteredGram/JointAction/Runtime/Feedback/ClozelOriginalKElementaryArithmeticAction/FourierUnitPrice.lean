import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitForwardFaces
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalFourierUnitPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKSourceResolventReconstruction
open OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "q" => (1/4:ℝ)

open private gamma gamma_ne_zero conjugate_zero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail
open private forward_unit_fourier_gap
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeWardCompactFee

private theorem source_left_adjoint (c:BurnolCompletedMellinCoordinate) (left value:BurnolL2) :
    inner ℂ (sourceResolvent c left) (F value)=inner ℂ left (F (R c value)) := by
  have right:1/4<(c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have starRight:1/4<(star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have adjoint:=congrArg (starRingEnd ℂ) (OriginalKCompactAdjointRSource.actual_original_R_adjoint
    (star c.value/2) starRight (F value) left)
  have transformed:=FiniteMobiusResolventFlux.fourier_R (c.value/2) right value
  change inner ℂ (sourceResolvent c left) (F value)=
    inner ℂ left (F (burnolDirectRightResolvent (c.value/2) value))
  simpa only [inner_conj_symm,sourceResolvent,star_div₀,star_ofNat,star_star,
    ←transformed] using adjoint

private theorem unit_fourier_pair (c:BurnolCompletedMellinCoordinate) (left value:BurnolL2) :
    inner ℂ (unitResolventSource c left) (F value)=
      star (star c.value*GapEuler.gapMean q c)*
        inner ℂ left (F (value-((1-c.value)/2) • R c value)) := by
  rw [unitResolventSource,inner_smul_left,inner_sub_left,inner_smul_left,source_left_adjoint]
  simp only [map_sub,map_smul,inner_sub_right,inner_smul_right,star_div₀,
    star_sub,star_one,star_ofNat,star_star,starRingEnd_apply]

/-- The original left unit action consumes the conjugate source's generated Fourier gap. -/
theorem elementary_fourier_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    inner ℂ (elementarySource c) (F ConstantForward.value)=0 := by
  have barValue:star (barC c).value=c.value := star_star c.value
  have barResolvent:sourceResolvent (barC c) ConstantForward.value=R c ConstantForward.value := by
    change burnolDirectRightResolvent (star (star c.value)/2) ConstantForward.value=_
    rw [star_star]
    rfl
  have unitNe:c.value*GapEuler.gapMean q (barC c)≠0 := by
    simpa only [gamma,barValue] using gamma_ne_zero (barC c)
  have gap:=UnitForwardFaces.forward_unit_fourier_gap (barC c) (conjugate_zero c zero)
  rw [unitResolventSource,barResolvent,barValue,map_smul,map_smul] at gap
  have localZero:burnolQuarterRestriction
      (F (ConstantForward.value-((1-c.value)/2) • R c ConstantForward.value))=0 :=
    (smul_eq_zero.mp gap).resolve_left unitNe
  have price:=ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction
    (F (ConstantForward.value-((1-c.value)/2) • R c ConstantForward.value)) (intervalConstant q)
  change inner ℂ ConstantDual.seed
    (F (ConstantForward.value-((1-c.value)/2) • R c ConstantForward.value))=_ at price
  rw [localZero,inner_zero_right] at price
  rw [←elementary_unit_resolvent c,unit_fourier_pair,price,mul_zero]

private theorem mean_zero_fourier_unit (test:BurnolQuarterMeanZeroCarrier) :
    inner ℂ (burnolQuarterZeroExtension (test:BurnolQuarterIntervalL2)) (F ConstantForward.value)=0 := by
  have price:=ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction
    (F ConstantForward.value) (test:BurnolQuarterIntervalL2)
  change inner ℂ (burnolQuarterZeroExtension (test:BurnolQuarterIntervalL2)) (F ConstantForward.value)=_ at price
  rw [price,forward_unit_fourier_gap,inner_smul_right]
  have mean:inner ℂ (test:BurnolQuarterIntervalL2) (intervalConstant q)=0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp test.property _
      (Submodule.mem_span_singleton_self _))
  rw [mean,mul_zero]

private theorem mean_zero_forward_unit (test:BurnolQuarterMeanZeroCarrier) :
    inner ℂ (burnolQuarterZeroExtension (test:BurnolQuarterIntervalL2)) ConstantForward.value=
      inner ℂ (test:BurnolQuarterIntervalL2) SmallScaleLog.logL2 := by
  have price:=ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction
    ConstantForward.value (test:BurnolQuarterIntervalL2)
  change inner ℂ (burnolQuarterZeroExtension (test:BurnolQuarterIntervalL2)) ConstantForward.value=_ at price
  rw [price,ConstantMean.forward_window,inner_add_right,inner_smul_right]
  have mean:inner ℂ (test:BurnolQuarterIntervalL2) (intervalConstant q)=0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp test.property _
      (Submodule.mem_span_singleton_self _))
  rw [mean,mul_zero,zero_add]

/-- The full original K correction retains its actual B-log contact after the unit action. -/
theorem kernel_fourier_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    inner ℂ (sourceKernel c) (F ConstantForward.value)=
      -inner ℂ (sourceB c:BurnolQuarterIntervalL2) SmallScaleLog.logL2 := by
  rw [sourceKernel,inner_sub_left,inner_add_left,elementary_fourier_unit c zero,
    mean_zero_fourier_unit,fourierL2.inner_map_map,mean_zero_forward_unit]
  simp only [add_zero,zero_sub]

end OriginalFourierUnitPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
