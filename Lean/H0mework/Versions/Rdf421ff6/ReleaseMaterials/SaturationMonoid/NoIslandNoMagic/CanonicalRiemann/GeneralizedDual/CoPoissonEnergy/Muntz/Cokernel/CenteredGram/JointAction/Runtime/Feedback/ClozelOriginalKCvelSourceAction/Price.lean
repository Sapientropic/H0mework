import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction

def actualCvelPairBoundaryStock (h t : ℝ) (N : ℕ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualVelocityIntegralPriceStock c test t N -
    OriginalRieszSource.Kernel.A c * OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h t +
    OriginalRieszSource.Kernel.beta c * OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h t

def actualCvelSiblingBoundaryStock (h t : ℝ) (N : ℕ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualVelocityIntegralPriceStock c test t N -
    OriginalRieszSource.Kernel.A c * OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h t -
    OriginalRieszSource.Kernel.beta c * OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h t

def actualCvelBoundaryStockPrice (h : ℝ) (N : ℕ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*(2*actualCvelPairBoundaryStock observation nontrivial half h h N) +
    star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*star (2*actualCvelSiblingBoundaryStock observation nontrivial half h h N)

def actualCvelBoundaryTailPrice (h : ℝ) (N : ℕ) : ℂ :=
  -(2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*
    actualVelocityIntegralPriceTail c (Q (actualNonPaPairedR observation nontrivial half h)) h N -
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*
    star (actualVelocityIntegralPriceTail c (Q (actualNonPaSiblingR observation nontrivial half h)) h N)

/-- The complete QB consumer uses the finite action price and its actual source tail; both contact windows remain paid source fields. -/
theorem actual_QB_boundary_consumes_Cvel_stock (h : ℝ) (N : ℕ) :
    OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice observation nontrivial half h =
      actualCvelBoundaryStockPrice observation nontrivial half h N + actualCvelBoundaryTailPrice observation nontrivial half h N := by
  unfold OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice
    OriginalKQBSourceWindowAction.actualNonPaPairBoundaryProgramme OriginalKQBSourceWindowAction.actualNonPaSiblingBoundaryProgramme
    actualCvelBoundaryStockPrice actualCvelPairBoundaryStock actualCvelSiblingBoundaryStock actualCvelBoundaryTailPrice
  dsimp only
  rw [actual_velocity_price_complete,actual_velocity_price_complete]
  simp only [star_add,star_sub,star_mul,star_ofNat,star_one]
  rw [show star (1/2:ℂ) = (1/2:ℂ) by norm_num]
  ring

def actualCvelTailBudget (h : ℝ) : ℝ :=
  ‖2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h‖ *
    (‖(Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2)‖+
      ‖(Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2)‖) *
    ((2*|h|)*((3/2:ℝ)*(‖OriginalRieszSource.Kernel.A c‖+‖OriginalRieszSource.Kernel.beta c‖))*‖OriginalRieszSource.Response.u‖)

theorem actual_Cvel_boundary_tail_bound (h : ℝ) (N : ℕ) :
    ‖actualCvelBoundaryTailPrice observation nontrivial half h N‖ ≤
      actualCvelTailBudget observation nontrivial half h * (1/4:ℝ)^N := by
  have bound := actual_velocity_integral_tail_bound c h N
  have pair := (norm_inner_le_norm (𝕜 := ℂ) (Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2)
    (actualVelocityIntegralTail c h N)).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))
  have sibling := (norm_inner_le_norm (𝕜 := ℂ) (Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2)
    (actualVelocityIntegralTail c h N)).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))
  unfold actualCvelBoundaryTailPrice
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_neg,norm_star]
  unfold actualVelocityIntegralPriceTail
  have pairPrice := mul_le_mul_of_nonneg_left pair
    (norm_nonneg (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h))
  have siblingPrice := mul_le_mul_of_nonneg_left sibling
    (norm_nonneg (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h))
  rw [norm_mul] at pairPrice siblingPrice
  exact (add_le_add pairPrice siblingPrice).trans_eq (by unfold actualCvelTailBudget; rw [norm_mul]; ring)

theorem actual_Cvel_boundary_stock_closure (h : ℝ) :
    Tendsto (actualCvelBoundaryStockPrice observation nontrivial half h) atTop
      (𝓝 (OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice observation nontrivial half h)) := by
  have pair := actual_velocity_price_stock_tendsto c (Q (actualNonPaPairedR observation nontrivial half h)) h
  have sibling := actual_velocity_price_stock_tendsto c (Q (actualNonPaSiblingR observation nontrivial half h)) h
  unfold actualCvelBoundaryStockPrice actualCvelPairBoundaryStock actualCvelSiblingBoundaryStock
    OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice OriginalKQBSourceWindowAction.actualNonPaPairBoundaryProgramme
    OriginalKQBSourceWindowAction.actualNonPaSiblingBoundaryProgramme
  dsimp only
  exact ((tendsto_const_nhds.mul (tendsto_const_nhds.mul
    (((tendsto_const_nhds.sub (tendsto_const_nhds.mul pair)).sub tendsto_const_nhds).add tendsto_const_nhds))).add
    (tendsto_const_nhds.mul ((tendsto_const_nhds.mul
      (((tendsto_const_nhds.sub (tendsto_const_nhds.mul sibling)).sub tendsto_const_nhds).sub tendsto_const_nhds)).star)))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
