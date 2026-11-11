import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.CompletePrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PhysicalPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.MixedBank
open scoped Topology InnerProductSpace
open private whole_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
open private paPowerField_price from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem evenPart_left (left right:BurnolL2) (even:reflectL2 right=right):
    inner ℂ (burnolAmbientEvenPart left) right=inner ℂ left right:=by
  have reflected:=reflectL2.inner_map_map left right
  rw [even] at reflected
  unfold burnolAmbientEvenPart
  rw [inner_smul_left,inner_add_left,reflected]
  simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
  norm_num
  ring

/-- Both feet are consumed on the same Whole; only their actual mean-zero Fourier price vanishes. -/
theorem actual_log_outside_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h) (k:ℕ):
    inner ℂ (logOutsideColumn d k) (wholeValue c zero h positive)=
      inner ℂ (logBFirst d k:Hq) (forwardQuarter c zero):=by
  rw [logOutsideColumn,evenPart_left _ _ (whole_even c zero h positive),inner_add_left,
    actual_meanZero_fourier_contact c zero h positive (logBSecond d k),add_zero]
  exact actual_compact_source_price c zero h positive (logBFirst d k)

theorem actual_source_outside_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h) (j:ℕ):
    inner ℂ (sourceOutside d j) (wholeValue c zero h positive)=
      ∑ k∈Finset.range j,star (sourceCoefficient d j k)*
        inner ℂ (logBFirst d k:Hq) (forwardQuarter c zero):=by
  simp only [sourceOutside,sum_inner,inner_smul_left,starRingEnd_apply,
    actual_log_outside_price c d zero h positive]

theorem actual_original_order_outside_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (fulladjointPowerZ observation half)
      (wholeValue c zero h positive-(burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2))=
      ∑ k∈Finset.range m,star (sourceCoefficient c m k)*
        inner ℂ (logBFirst c k:Hq) (forwardQuarter c zero):=by
  dsimp only
  have same:burnolDivisionZeroCompletedMellinCoordinate (burnolPaZeroObservation c zero) c.rightHalf=c:=by
    cases c
    rfl
  rw [OriginalKFiniteOrderRelease.UnitPowerJordanSource.actual_outside_price
    (burnolPaZeroObservation c zero) ⟨c.rightHalf⟩,same]
  apply Finset.sum_congr rfl
  intro k inside
  rw [actual_log_outside_price c c zero h positive k]

/-- The original full m price retains its whole-Pa coefficient, physical residual and fully generated outside bank. -/
theorem actual_original_full_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (wholeValue c zero h positive))=
      feedbackCoefficient observation half*
        burnolPaResolventSourceCoefficient c (OriginalKCombCofinalPaAction.E (wholeValue c zero h positive))+
      inner ℂ (sourceQ observation half) (wholeValue c zero h positive)+
      ∑ k∈Finset.range m,star (sourceCoefficient c m k)*
        inner ℂ (logBFirst c k:Hq) (forwardQuarter c zero):=by
  dsimp only
  let observation:=burnolPaZeroObservation c zero
  let nontrivial:=burnolPaZeroObservation_nontrivial c zero
  let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
  let value:=wholeValue c zero h positive
  have same:burnolDivisionZeroCompletedMellinCoordinate observation half.down=c:=by
    cases c
    rfl
  have fieldPa:paPowerField observation half∈burnolCompactCoPoissonClosedRange:=by
    rw [←actual_adjoint_power_Pa_source observation nontrivial half]
    exact Submodule.starProjection_apply_mem _ _
  have paRead:=OriginalKCombCofinalPaAction.wholePa_normal_read value (paPowerField observation half) fieldPa
  have paPrice:inner ℂ (paPowerField observation half:BurnolL2) value=
      feedbackCoefficient observation half*burnolPaResolventSourceCoefficient c (OriginalKCombCofinalPaAction.E value):=by
    rw [←paRead]
    exact paPowerField_price observation half (OriginalKCombCofinalPaAction.E value) (Submodule.starProjection_apply_mem _ _)
  have read:=actual_full_power_read observation half value
  change inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
    (CombSource.Division.rawIterate observation half.down
      (generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate) value)=
        inner ℂ (fulladjointPowerZ observation half) value at read
  rw [read,
    source_full_inventory observation half,inner_add_left,inner_add_left,paPrice,same,
    actual_source_outside_price c c zero h positive]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PhysicalPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
