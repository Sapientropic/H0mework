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
namespace OriginalKCrossParameterRAdjointSource.CrossUnitKSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction
open scoped InnerProductSpace
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance crossUnitPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem coordinate_eq {left right : BurnolCompletedMellinCoordinate}
 (same : left.value=right.value) : left=right := by
 cases left
 cases right
 cases same
 rfl

private theorem ambient_physical_read (read : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
 burnolAmbientCompletedMellinEvaluator read (value : BurnolL2)=inner ℂ (K read : BurnolL2) (value : BurnolL2) := by
 have restrict:=congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ=>f value)
  (burnolAmbientCompletedMellinEvaluator_restrict read)
 change burnolAmbientCompletedMellinEvaluator read (value : BurnolL2)=burnolCompletedMellinEvaluator read value at restrict
 exact restrict.trans (burnolCompletedMellinRieszVector_readback read value).symm

/-- The action parameter is the original comb source; its dependent read parameter stays independent. -/
private theorem original_comb_cross_response_price_zero (observation : GeneratedRiemannZeroObservation)
 (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
 (half : OriginalKCombCalculation.Half observation) (read : BurnolCompletedMellinCoordinate)
 (readZero : riemannZeta read.value=0) :
 let c:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
 inner ℂ (K read : BurnolL2)
  (burnolDirectRightResolvent (c.value/2) (burnolPaCombApproximation 0 : BurnolL2))=0 := by
 dsimp only
 let c:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
 have right : 1/4<(c.value/2).re := by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
 have readRight : 1/4<(read.value/2).re := by rw [Complex.div_re];norm_num;linarith [read.rightHalf]
 have readBelow : (read.value/2).re<1/2 := by rw [Complex.div_re];norm_num;linarith [read.belowOne]
 have sameRead : burnolDivisionCompletedMellinCoordinate (read.value/2) readRight readBelow=read := by
  apply coordinate_eq
  change 2*(read.value/2)=read.value
  ring
 have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal read readZero
 have inputZero : inner ℂ (K read : BurnolL2) (burnolPaCombApproximation 0 : BurnolL2)=0 :=
  inner_eq_zero_symm.mp (orthogonal (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0))
 have scalar:=CombSource.Pricing.ambient_R_scalar_action (c.value/2) right
  (burnolPaCombApproximation 0 : BurnolL2) (burnolPaCombApproximation 0).property.1.1
  (read.value/2) readRight readBelow
 rw [sameRead,ambient_physical_read read (burnolPaCombApproximation 0),inputZero,mul_zero] at scalar
 let response:=burnolPaCombPhysicalResponse observation nontrivial half.down 0
 have responseRead : (response : BurnolL2)=
   burnolDirectRightResolvent (c.value/2) (burnolPaCombApproximation 0 : BurnolL2) := by
  dsimp only [response,burnolPaCombPhysicalResponse]
  rfl
 rw [←responseRead,ambient_physical_read] at scalar
 simpa only [responseRead] using scalar

/-- The same nonzero original source coefficient and original source shell pay both unit prices. -/
private theorem original_unit_cross_prices (observation : GeneratedRiemannZeroObservation)
 (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
 (half : OriginalKCombCalculation.Half observation) (read : BurnolCompletedMellinCoordinate)
 (readZero : riemannZeta read.value=0) :
 let c:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
 inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 1)=0 ∧
 inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 4)=0 := by
 dsimp only
 let c:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
 have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal read readZero
 let Q:=burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
 have normal (value : BurnolPaAmbientCarrier) : inner ℂ (K read) (Q value)=inner ℂ (K read) value :=
  burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
   ⟨K read,orthogonal⟩ value
 have responseZero:=original_comb_cross_response_price_zero observation nontrivial half read readZero
 dsimp only at responseZero
 change inner ℂ (K read) (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=0 at responseZero
 have unitRead:=congrArg (inner ℂ (K read)) (burnolPaCombPhysicalResponse_scaledQ observation nontrivial half.down 0)
 rw [inner_smul_right,inner_smul_right] at unitRead
 simp only [Nat.cast_zero] at unitRead
 change (observation.coordinate/2)*inner ℂ (K read) (Q (burnolPaCombPhysicalResponse observation nontrivial half.down 0))=
  ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)*
   inner ℂ (K read) (Q (burnolZeroOwnedUnitOneState observation nontrivial half.down)) at unitRead
 rw [normal,normal,responseZero,mul_zero] at unitRead
 have factorNe : ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)≠0 := by
  have coefficient:=burnolPaCombResponseCoefficient_ne_zero observation.coordinate (by linarith [half.down]) 0
  intro zero
  apply coefficient
  unfold burnolPaCombResponseCoefficient
  simp only [Nat.cast_zero]
  rw [div_mul_eq_mul_div,zero,zero_div]
 have unitOneZero:=(mul_eq_zero.mp unitRead.symm).resolve_left factorNe
 change inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 1)=0 at unitOneZero
 obtain ⟨wave,wavePa,waveRead⟩:=Submodule.mem_map.mp
  (burnolUnitPowerShellWave_originalPa c 1 (by norm_num) (by norm_num))
 have shellZero : inner ℂ (K read : BurnolL2) (wave : BurnolL2)=0 :=
  inner_eq_zero_symm.mp (orthogonal wave wavePa)
 have shell:=burnolUnitTailResponse_shell c 1 (by norm_num) (by norm_num)
 rw [←waveRead] at shell
 have price:=congrArg (inner ℂ (K read : BurnolL2)) shell
 rw [inner_sub_right] at price
 change inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 1)-
  inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 4)=inner ℂ (K read : BurnolL2) (wave : BurnolL2) at price
 rw [unitOneZero,shellZero] at price
 have unitFourZero : inner ℂ (K read : BurnolL2) (burnolUnitTailResponse c 4)=0 := by linear_combination -price
 exact ⟨unitOneZero,unitFourZero⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
include nontrivial

/-- The original c-source is priced by its same-owner conjugate zero face. -/
theorem conjugate_K_original_unit_price_zero :
 inner ℂ (generatedK (barC c)) (burnolUnitTailResponse c 4)=0 := by
 have conjugateZero : riemannZeta (barC c).value=0 := observation.conjugate_mathlibZero
 rw [generatedK_eq_original]
 exact (original_unit_cross_prices observation nontrivial half (barC c) conjugateZero).2

/-- Conjugation changes only the mathematical source parameter, with the original owner fixed. -/
theorem original_K_conjugate_unit_price_zero :
 inner ℂ (generatedK c) (burnolUnitTailResponse (barC c) 4)=0 := by
 let conjugateObservation:=GeneratedRiemannZeroObservationAt.ofMathlibZero ActualAnalyticOwner
  (starRingEnd ℂ observation.coordinate) observation.conjugate_mathlibZero
 have conjugateNontrivial : ¬∃ n:Nat,conjugateObservation.coordinate=-2*(n+1) :=
  observation.conjugate_nontrivial nontrivial
 let conjugateHalf : OriginalKCombCalculation.Half conjugateObservation:=
  ⟨by
   change 1/2<(starRingEnd ℂ observation.coordinate).re
   simpa only [Complex.conj_re] using half.down⟩
 have same : burnolDivisionZeroCompletedMellinCoordinate conjugateObservation conjugateHalf.down=barC c := by
  apply coordinate_eq
  rfl
 have generated:=original_unit_cross_prices conjugateObservation conjugateNontrivial conjugateHalf c observation.mathlibZero
 dsimp only at generated
 rw [same] at generated
 rw [generatedK_eq_original]
 exact generated.2

/-- Actual Fourier transports this cross price to the complete FK Pa-return source coefficient. -/
theorem conjugate_unit_FK_reentry_price_zero :
 inner ℂ (fourierL2 (burnolUnitTailResponse (barC c) 4)) (fourierL2 (generatedK c))=0 := by
 exact (fourierL2.inner_map_map _ _).trans
  (inner_eq_zero_symm.mp (original_K_conjugate_unit_price_zero observation nontrivial half))

end OriginalKCrossParameterRAdjointSource.CrossUnitKSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
