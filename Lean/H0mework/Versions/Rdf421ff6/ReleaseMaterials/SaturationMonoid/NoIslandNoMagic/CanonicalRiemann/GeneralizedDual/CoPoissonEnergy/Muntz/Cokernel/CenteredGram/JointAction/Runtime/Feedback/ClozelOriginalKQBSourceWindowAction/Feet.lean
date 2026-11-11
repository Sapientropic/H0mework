import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance qbFeetComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction
private theorem source_Q_F_covariance (x : BurnolL2) : Q (fourierL2 x) = F (Q x) := by
  have physical : P (fourierL2 x) = F (P x) := by
    apply Subtype.ext
    exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius x).symm
  have pa := congrArg (fun value : SourceGeneratedHilbertCokernel.OrthogonalResidual
      burnolCompactCoPoissonLanding => (value : BurnolPaAmbientCarrier))
    (burnolCompactCoPoissonActionSquare.orthogonalAction_residual (P x))
  change F (Q x) = burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection (F (P x)) at pa
  change burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection (P (fourierL2 x)) = _
  rw [physical]
  exact pa.symm

/-- The source Fourier covariance gives the two projected R directions their actual signs before contact prices. -/
theorem actual_nonPa_Q_fourier_feet (h : ℝ) :
    F (Q (actualNonPaPairedR observation nontrivial half h)) =
      Q (actualNonPaPairedR observation nontrivial half h) ∧
    F (Q (actualNonPaSiblingR observation nontrivial half h)) =
      -Q (actualNonPaSiblingR observation nontrivial half h) := by
  unfold actualNonPaPairedR actualNonPaSiblingR OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
  simp only [map_smul,map_add,map_sub]
  simp only [source_Q_F_covariance]
  have twice : F (F (Q (actualNonPaR observation nontrivial half h))) =
      Q (actualNonPaR observation nontrivial half h) :=
    evenFaceFourier_involutive burnolUnscaledCommonGapRadius _
  rw [twice]
  constructor <;> module

def actualNonPaPairSeedProgramme (h t : ℝ) : ℂ :=
  (1/4:ℂ) * (star ((Real.exp (-t/2):ℂ)*actualNonPaPairMeanProgramme observation nontrivial half h 0) +
    star (actualNonPaPairMeanProgramme observation nontrivial half h t) -
    2*star (actualNonPaPairMeanProgramme observation nontrivial half h 0))
def actualNonPaSiblingSeedProgramme (h t : ℝ) : ℂ :=
  (1/4:ℂ) * (star ((Real.exp (-t/2):ℂ)*actualNonPaSiblingMeanProgramme observation nontrivial half h 0) +
    star (actualNonPaSiblingMeanProgramme observation nontrivial half h t) -
    2*star (actualNonPaSiblingMeanProgramme observation nontrivial half h 0))

private theorem source_seed_price_neg (value : BurnolPaAmbientCarrier) (t : ℝ) :
    OriginalKBoundarySourceAction.actualSeedWindowPrice (-value) t =
      -OriginalKBoundarySourceAction.actualSeedWindowPrice value t := by
  unfold OriginalKBoundarySourceAction.actualSeedWindowPrice
  simp only [Submodule.coe_neg,map_neg,star_neg]
  ring

/-- The complete four QB contacts now consume generated finite source programmes, including the hidden Pa projection and every original unit fee. -/
theorem actual_nonPa_four_source_contact_prices (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualSeedWindowPrice (Q (actualNonPaPairedR observation nontrivial half h)) t =
      actualNonPaPairSeedProgramme observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice (F (Q (actualNonPaPairedR observation nontrivial half h))) t =
      actualNonPaPairSeedProgramme observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice (Q (actualNonPaSiblingR observation nontrivial half h)) t =
      actualNonPaSiblingSeedProgramme observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice (F (Q (actualNonPaSiblingR observation nontrivial half h))) t =
      -actualNonPaSiblingSeedProgramme observation nontrivial half h t := by
  have initial := actual_nonPa_positive_mean_programmes observation nontrivial half h nonnegative bounded 0 le_rfl
  simp only [burnolMultiplicativeDilation_zero] at initial
  have expanded := actual_nonPa_positive_mean_programmes observation nontrivial half h nonnegative bounded t positive
  have contractedPair := FiniteMobiusResolventFlux.actual_mean_source_negative
    (Q (actualNonPaPairedR observation nontrivial half h)) (-t) (neg_nonpos.mpr positive)
  have contractedSibling := FiniteMobiusResolventFlux.actual_mean_source_negative
    (Q (actualNonPaSiblingR observation nontrivial half h)) (-t) (neg_nonpos.mpr positive)
  have pair : OriginalKBoundarySourceAction.actualSeedWindowPrice (Q (actualNonPaPairedR observation nontrivial half h)) t =
      actualNonPaPairSeedProgramme observation nontrivial half h t := by
    unfold OriginalKBoundarySourceAction.actualSeedWindowPrice actualNonPaPairSeedProgramme
    rw [contractedPair,initial.1,expanded.1]
  have sibling : OriginalKBoundarySourceAction.actualSeedWindowPrice (Q (actualNonPaSiblingR observation nontrivial half h)) t =
      actualNonPaSiblingSeedProgramme observation nontrivial half h t := by
    unfold OriginalKBoundarySourceAction.actualSeedWindowPrice actualNonPaSiblingSeedProgramme
    rw [contractedSibling,initial.2,expanded.2]
  have feet := actual_nonPa_Q_fourier_feet observation nontrivial half h
  refine ⟨pair,?_,sibling,?_⟩
  · rw [feet.1]
    exact pair
  · rw [feet.2,source_seed_price_neg,sibling]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
