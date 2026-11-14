import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceJointTail
import Mathlib.Topology.Baire.CompleteMetrizable

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceCountable

open BurnolPhysicalState Filter Set
open scoped Topology InnerProductSpace
open private probe from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.MellinSeparation
open private continuous_probe_price probe_real from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceGrid
open private wholePrice whole_price_analytic original_price strip_connected probe_continuous
  probe_injective probe_in_strip from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceJointTail

def coordinate (height : ℝ) : BurnolCompletedMellinCoordinate := probe height

def price (height : ℝ) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  burnolCompletedMellinEvaluator (coordinate height)

theorem real_part (height : ℝ) : (coordinate height).value.re = 3/4 := probe_real height

theorem price_is_original_K (height : ℝ) (value : BurnolPaAmbientCarrier) :
    price height value =
      inner ℂ (burnolCompletedMellinRieszVector (coordinate height) : BurnolL2) (value : BurnolL2) :=
  (burnolCompletedMellinRieszVector_readback (coordinate height) value).symm

private theorem live_dense (value : BurnolPaAmbientCarrier) (live : value ≠ 0) :
    Dense {height : ℝ | price height value ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U openU inside
  by_contra missing
  obtain ⟨anchor,member⟩ := inside
  have quiet (height : ℝ) (within : height ∈ U) : wholePrice value (probe height).value = 0 := by
    rw [original_price]
    by_contra nonzero
    exact missing ⟨height,within,nonzero⟩
  have goes : Tendsto (fun y : ℝ => (probe y).value) (𝓝[≠] anchor) (𝓝[≠] (probe anchor).value) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨probe_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    exact eventually_mem_nhdsWithin.mono fun y ne => fun same => ne (probe_injective same)
  have nearAnchor : ∀ᶠ y in 𝓝 anchor, y ∈ U := openU.mem_nhds member
  have often : ∃ᶠ z in 𝓝[≠] (probe anchor).value, wholePrice value z = 0 :=
    goes.frequently ((nearAnchor.filter_mono nhdsWithin_le_nhds).mono quiet).frequently
  have zero := (whole_price_analytic value).eqOn_zero_of_preconnected_of_frequently_eq_zero
    strip_connected (probe_in_strip anchor) often
  apply live (PhysicalPriceGrid.tail_separates value 0 ?_)
  intro t
  let q := PhysicalPriceGrid.coordinate (0+t)
  change burnolCompletedMellinEvaluator q value = 0
  rw [← original_price]
  exact zero (show q.value ∈ _ from ⟨q.rightHalf,q.belowOne⟩)

/-- One original K query may be chosen beyond any height for all countably many live physical fields. -/
theorem exists_after {ι : Type*} [Countable ι] (fields : ι → BurnolPaAmbientCarrier)
    (live : ∀ i, fields i ≠ 0) (lower : ℝ) :
    ∃ height : ℝ, lower < height ∧ ∀ i, price height (fields i) ≠ 0 := by
  let openLive (i : ι) : Set ℝ := {height | price height (fields i) ≠ 0}
  have dense : Dense (⋂ i, openLive i) :=
    dense_iInter_of_isOpen (fun i => isOpen_ne_fun (continuous_probe_price (fields i)) continuous_const)
      (fun i => live_dense (fields i) (live i))
  obtain ⟨height, chosen, after⟩ := dense.exists_mem_open isOpen_Ioi
    (show (Ioi lower).Nonempty from ⟨lower+1,by simp⟩)
  exact ⟨height,after,fun i => mem_iInter.mp chosen i⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceCountable
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
