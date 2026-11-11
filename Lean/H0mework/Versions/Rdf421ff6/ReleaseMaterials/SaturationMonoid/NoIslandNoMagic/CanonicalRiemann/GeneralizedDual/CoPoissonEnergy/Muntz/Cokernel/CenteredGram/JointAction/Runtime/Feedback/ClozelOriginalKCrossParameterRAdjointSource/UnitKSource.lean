import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKAmbientPricing
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Class

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.UnitKSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction
open scoped InnerProductSpace
local notation "K" => burnolCompletedMellinRieszVector
local instance unitKPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem coordinate_eq {left right : BurnolCompletedMellinCoordinate}
    (same : left.value=right.value) : left=right := by
  cases left
  cases right
  cases same
  rfl

private theorem ambient_physical_read (c : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
    burnolAmbientCompletedMellinEvaluator c (value : BurnolL2)=inner ℂ (K c : BurnolL2) (value : BurnolL2) := by
  have restrict := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f value)
    (burnolAmbientCompletedMellinEvaluator_restrict c)
  change burnolAmbientCompletedMellinEvaluator c (value : BurnolL2)=burnolCompletedMellinEvaluator c value at restrict
  exact restrict.trans (burnolCompletedMellinRieszVector_readback c value).symm

/-- The original comb0's full physical R response has zero K price by its actual ambient scalar action. -/
theorem comb_response_K_price_zero (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) :
    let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    inner ℂ (K c : BurnolL2)
      (burnolDirectRightResolvent (c.value/2) (burnolPaCombApproximation 0 : BurnolL2))=0 := by
  dsimp only
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  have right : 1/4<(c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have below : (c.value/2).re<1/2 := by
    rw [Complex.div_re];norm_num;linarith [c.belowOne]
  have same : burnolDivisionCompletedMellinCoordinate (c.value/2) right below=c := by
    apply coordinate_eq
    change 2*(c.value/2)=c.value
    ring
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have inputZero : inner ℂ (K c : BurnolL2) (burnolPaCombApproximation 0 : BurnolL2)=0 :=
    inner_eq_zero_symm.mp (orthogonal (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0))
  have scalar := CombSource.Pricing.ambient_R_scalar_action (c.value/2) right
    (burnolPaCombApproximation 0 : BurnolL2) (burnolPaCombApproximation 0).property.1.1
    (c.value/2) right below
  rw [same,ambient_physical_read c (burnolPaCombApproximation 0),inputZero,mul_zero] at scalar
  let response := burnolPaCombPhysicalResponse observation nontrivial half.down 0
  have responseRead : (response : BurnolL2)=
      burnolDirectRightResolvent (c.value/2) (burnolPaCombApproximation 0 : BurnolL2) := by
    dsimp only [response,burnolPaCombPhysicalResponse]
    rw [show c.value=observation.coordinate from OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half]
  rw [←responseRead,ambient_physical_read] at scalar
  simpa only [responseRead] using scalar

/-- A nonzero coefficient from that same finite comb source isolates unit1; the actual Pa shell then pays unit4. -/
theorem wholeUnitSourcePrice_zero (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) :
    wholeUnitSourcePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)=0 := by
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  have same : burnolDivisionZeroCompletedMellinCoordinate observation half.down=c := by
    apply coordinate_eq
    rfl
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  have normal (value : BurnolPaAmbientCarrier) : inner ℂ (K c) (Q value)=inner ℂ (K c) value :=
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨K c,orthogonal⟩ value
  have responseZero := comb_response_K_price_zero observation nontrivial half
  dsimp only at responseZero
  change inner ℂ (K c) (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=0 at responseZero
  have unitRead := congrArg (inner ℂ (K c))
    (burnolPaCombPhysicalResponse_scaledQ observation nontrivial half.down 0)
  rw [inner_smul_right,inner_smul_right] at unitRead
  simp only [Nat.cast_zero] at unitRead
  change (observation.coordinate/2)*inner ℂ (K c) (Q (burnolPaCombPhysicalResponse observation nontrivial half.down 0))=
    ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)*
      inner ℂ (K c) (Q (burnolZeroOwnedUnitOneState observation nontrivial half.down)) at unitRead
  rw [normal,normal,responseZero,mul_zero] at unitRead
  have factorNe : ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)≠0 := by
    have coefficient := burnolPaCombResponseCoefficient_ne_zero observation.coordinate
      (by linarith [half.down]) 0
    intro zero
    apply coefficient
    unfold burnolPaCombResponseCoefficient
    simp only [Nat.cast_zero]
    rw [div_mul_eq_mul_div,zero,zero_div]
  have unitOneZero := (mul_eq_zero.mp unitRead.symm).resolve_left factorNe
  change inner ℂ (K c : BurnolL2) (burnolUnitTailResponse
    (burnolDivisionZeroCompletedMellinCoordinate observation half.down) 1)=0 at unitOneZero
  rw [same] at unitOneZero
  obtain ⟨wave,wavePa,waveRead⟩ := Submodule.mem_map.mp
    (burnolUnitPowerShellWave_originalPa c 1 (by norm_num) (by norm_num))
  have shellZero : inner ℂ (K c : BurnolL2) (wave : BurnolL2)=0 :=
    inner_eq_zero_symm.mp (orthogonal wave wavePa)
  have shell := burnolUnitTailResponse_shell c 1 (by norm_num) (by norm_num)
  rw [←waveRead] at shell
  have price := congrArg (inner ℂ (K c : BurnolL2)) shell
  rw [inner_sub_right] at price
  change inner ℂ (K c : BurnolL2) (burnolUnitTailResponse c 1)-inner ℂ (K c : BurnolL2) (burnolUnitTailResponse c 4)=
    inner ℂ (K c : BurnolL2) (wave : BurnolL2) at price
  rw [unitOneZero,shellZero] at price
  have unitFourZero : inner ℂ (K c : BurnolL2) (burnolUnitTailResponse c 4)=0 := by
    linear_combination -price
  unfold wholeUnitSourcePrice
  rw [generatedK_eq_original]
  exact unitFourZero

end OriginalKCrossParameterRAdjointSource.UnitKSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
