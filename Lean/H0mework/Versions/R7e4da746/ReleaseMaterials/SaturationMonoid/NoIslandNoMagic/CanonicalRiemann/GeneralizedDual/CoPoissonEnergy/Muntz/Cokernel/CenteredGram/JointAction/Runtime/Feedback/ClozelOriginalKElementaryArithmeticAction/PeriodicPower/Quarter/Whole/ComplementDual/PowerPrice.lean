import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

theorem actual_floor_quarter_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (Rq (fullFloorValue c zero):ℝ→ℂ)=ᵐ[μq]fullFloorRaw c:=
  (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (fullFloorValue c zero)).trans
    (ae_restrict_of_ae (actual_full_floor_raw c zero))

theorem actual_floor_compact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    E (Rq (fullFloorValue c zero))=fullFloorValue c zero:=by
  apply Lp.ext
  have localRead:∀ᵐx:ℝ ∂volume,x∈symmetricInterval q→
      Rq (fullFloorValue c zero) x=fullFloorRaw c x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (actual_floor_quarter_raw c zero)
  filter_upwards [burnolRadiusZeroExtension_coe (Rq (fullFloorValue c zero)),localRead,
    actual_full_floor_raw c zero] with x extended localSource actual
  change burnolRadiusZeroExtension q (Rq (fullFloorValue c zero)) x=_
  rw [extended,actual]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,localSource inside]
  · rw [indicator_of_notMem inside]
    exact (actual_floor_outer_zero c.value c.belowOne x
      (lt_of_not_ge (fun bounded=>inside (abs_le.mp bounded)))).symm

/-- The original exact-m action reads the same fully generated unweighted compact counting field. -/
theorem actual_original_count_power_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (fullFloorValue c zero))=
      (star (sourceConstant c m)/2)*burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero))+
      ∑k∈Finset.range m,star (sourceCoefficient c m k)*(2/(k.factorial:ℂ))*logMoment c k (fullFloorRaw c):=by
  have source:=actual_original_compact_log_price c zero (Rq (fullFloorValue c zero))
    (fullFloorRaw c) (actual_floor_quarter_raw c zero) (actual_floor_even c.value c.belowOne)
  dsimp only at source ⊢
  rw [actual_floor_compact c zero] at source
  exact source

def conjugateHalf (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    OriginalKCombCalculation.Half (conjugateZeroObservation (burnolPaZeroObservation c zero)):=⟨by
  change 1/2<(starRingEnd ℂ c.value).re
  simpa only [conj_re] using c.rightHalf⟩

/-- Conjugation changes the actual action parameter while the original owner supplies the same m. -/
theorem actual_conjugate_original_count_power_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    let observation:=burnolPaZeroObservation c zero
    let reflected:=conjugateZeroObservation observation
    let half:=conjugateHalf c zero
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo (barC c))
      (CombSource.Division.rawIterate reflected half.down m (fullFloorValue c zero))=
      (star (sourceConstant (barC c) m)/2)*burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero))+
      ∑k∈Finset.range m,star (sourceCoefficient (barC c) m k)*(2/(k.factorial:ℂ))*
        logMoment (barC c) k (fullFloorRaw c):=by
  dsimp only
  have reflectedZero:riemannZeta (barC c).value=0:=
    (conjugateZeroObservation (burnolPaZeroObservation c zero)).mathlibZero
  have source:=actual_original_compact_log_price (barC c) reflectedZero
    (Rq (fullFloorValue c zero)) (fullFloorRaw c) (actual_floor_quarter_raw c zero)
    (actual_floor_even c.value c.belowOne)
  dsimp only at source
  change inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo (barC c))
    (CombSource.Division.rawIterate (conjugateZeroObservation (burnolPaZeroObservation c zero))
      (conjugateHalf c zero).down
      (generatedRiemannXiZeroOrder ActualAnalyticOwner (star c.value))
      (E (Rq (fullFloorValue c zero))))=_ at source
  rw [show (burnolPaZeroObservation (barC c) reflectedZero).coordinate=star c.value from rfl,
    actual_floor_compact c zero,
    OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
