import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local instance feetComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction

def actualCoupledSourcePlus : BurnolL2 := Response.wholeU + Response.wholeV
def actualCoupledSourceMinus : BurnolL2 := Response.wholeU - Response.wholeV

private theorem expanded_source_add (test : BurnolPaAmbientCarrier) (left right : BurnolL2) (h : ℝ) :
    actualExpandedSourceRead test (left+right) h = actualExpandedSourceRead test left h + actualExpandedSourceRead test right h := by
  unfold actualExpandedSourceRead
  simp only [map_add,inner_add_right]
  exact intervalIntegral.integral_add
    (((innerSL ℂ (test : BurnolL2)).continuous.comp
      ((burnolMultiplicativeDilation_stronglyContinuous left).comp continuous_neg)).intervalIntegrable 0 h)
    (((innerSL ℂ (test : BurnolL2)).continuous.comp
      ((burnolMultiplicativeDilation_stronglyContinuous right).comp continuous_neg)).intervalIntegrable 0 h)

private theorem expanded_source_sub (test : BurnolPaAmbientCarrier) (left right : BurnolL2) (h : ℝ) :
    actualExpandedSourceRead test (left-right) h = actualExpandedSourceRead test left h - actualExpandedSourceRead test right h := by
  unfold actualExpandedSourceRead
  simp only [map_sub,inner_sub_right]
  exact intervalIntegral.integral_sub
    (((innerSL ℂ (test : BurnolL2)).continuous.comp
      ((burnolMultiplicativeDilation_stronglyContinuous left).comp continuous_neg)).intervalIntegrable 0 h)
    (((innerSL ℂ (test : BurnolL2)).continuous.comp
      ((burnolMultiplicativeDilation_stronglyContinuous right).comp continuous_neg)).intervalIntegrable 0 h)

private theorem expanded_test_neg (test : BurnolPaAmbientCarrier) (source : BurnolL2) (h : ℝ) :
    actualExpandedSourceRead (-test) source h = -actualExpandedSourceRead test source h := by
  unfold actualExpandedSourceRead
  simp only [Submodule.coe_neg,inner_neg_left,intervalIntegral.integral_neg]

def actualPairCvelSourcePrice (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  actualContactVelocityPrice c test t + (Kernel.A c-Kernel.beta c)*actualExpandedSourceRead test actualCoupledSourcePlus t

def actualSiblingCvelSourcePrice (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  actualContactVelocityPrice c test t - (Kernel.A c+Kernel.beta c)*actualExpandedSourceRead test actualCoupledSourceMinus t

/-- The two original QNP Fourier faces read complete U+V and U-V expansion fields after source compression. -/
theorem actual_pair_sibling_Cvel_source_prices (h t : ℝ) (nonnegative : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c
      (Q (actualNonPaPairedR observation nontrivial half h)) t = actualPairCvelSourcePrice observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c
      (Q (actualNonPaSiblingR observation nontrivial half h)) t = actualSiblingCvelSourcePrice observation nontrivial half h t := by
  have faces := OriginalKQBSourceWindowAction.actual_nonPa_Q_fourier_feet observation nontrivial half h
  constructor
  · rw [actual_Cvel_contact_inventory_price,actual_response_velocity_compressed_price c _ t nonnegative,faces.1]
    unfold actualPairCvelSourcePrice actualCoupledSourcePlus
    dsimp only
    rw [expanded_source_add]
    ring
  · rw [actual_Cvel_contact_inventory_price,actual_response_velocity_compressed_price c _ t nonnegative,faces.2,
      expanded_test_neg,expanded_test_neg]
    unfold actualSiblingCvelSourcePrice actualCoupledSourceMinus
    dsimp only
    rw [expanded_source_sub]
    ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
