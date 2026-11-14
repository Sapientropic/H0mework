import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.TwoReceiptReturn

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 155000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
attribute [local instance] DivisionEffectPrice.wideNormed

open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
open private adjointWord from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private word_power from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ReentryDifferenceClock
open private adjoint_R from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape
open private source_right_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

def directReturnMap (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
  let includePa := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  (Pa.sourceReentryAction c).comp (1 - includePa.comp Pa.E)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (sourceDamping c : ℂ)
local notation "R" => burnolDirectRightResolventCLM c
local notation "word" => adjointWord observation nontrivial half
local notation "source" => paid observation nontrivial half depth
local notation "returns" => paReturn observation nontrivial half depth
local notation "direct" => directReturnMap c

def adjointReturnMap : Wide →L[ℂ] BurnolPaAmbientCarrier :=
  (direct).comp ((word).comp readField)

/-- Compare the next graph already written at the first ordinal with the graph read at the second. -/
def graphOverlap (n m : Nat) : Wide :=
  (source (ordinal+1) n m).2.1 - (source ordinal n m).2.2

private theorem adjoint_removal (x : BurnolL2) : word x + δ • word (R x) = x := by
  have identity : word = (sourceCayley c).adjoint := by
    rw [word_power observation nontrivial half, TwoReceiptReturn.exit_one observation nontrivial half,
      pow_one]
  rw [identity, adjoint_R]
  exact (sourceCayley_apply c ((sourceCayley c).adjoint x)).symm.trans (source_right_inverse c x)

theorem pa_return_map (n m : Nat) :
    returns ordinal n m = adjointReturnMap observation nontrivial half (source ordinal n m).2.1 :=
  pa_return_eq observation nontrivial half depth ordinal n m

private theorem direct_return_eq (x : BurnolL2) :
    direct x = Pa.E (R x) - Pa.E (R (Pa.E x : BurnolL2)) := by
  change Pa.sourceReentryAction c (Pa.invisible x) = _
  rw [← Pa.full_invisible_reentry]
  change Pa.E (R (x-(Pa.E x : BurnolL2))) = _
  rw [map_sub, map_sub]

theorem direct_paid_return (n m : Nat) :
    direct (readField (source ordinal n m).2.1) =
      Pa.E (readField (source ordinal n m).2.2) -
        Pa.E (R (Pa.E (readField (source ordinal n m).2.1) : BurnolL2)) := by
  rw [field_next observation nontrivial half depth ordinal n m, direct_return_eq observation half]

attribute [local irreducible] paid in
/-- Two adjacent paid adjoint returns recover the direct Pa write with its exact finite overlap term. -/
theorem two_paid_pa_returns (n m : Nat) :
    returns ordinal n m + δ • returns (ordinal+1) n m =
      direct (readField (source ordinal n m).2.1) +
        δ • adjointReturnMap observation nontrivial half
          (graphOverlap observation nontrivial half depth ordinal n m) := by
  let x := (source ordinal n m).2.1
  let y := (source ordinal n m).2.2
  let z := (source (ordinal+1) n m).2.1
  let response := adjointReturnMap observation nontrivial half
  have lifted : response x + δ • response y = direct (readField x) := by
    change direct (word (readField x)) + δ • direct (word (readField y)) = _
    rw [← map_smul, ← map_add, field_next observation nontrivial half depth ordinal n m,
      adjoint_removal observation nontrivial half]
  have old : returns ordinal n m = response x :=
    pa_return_map observation nontrivial half depth ordinal n m
  have next : returns (ordinal+1) n m = response z :=
    pa_return_map observation nontrivial half depth (ordinal+1) n m
  let gap := graphOverlap observation nontrivial half depth ordinal n m
  have overlap : gap = z-y := rfl
  have balance : response x + δ • response z =
      (response x + δ • response y) + δ • response gap := by
    rw [overlap, map_sub, smul_sub]
    abel
  have correction : (response x + δ • response y) + δ • response gap =
      direct (readField x) + δ • response gap :=
    congrArg (fun a : BurnolPaAmbientCarrier => a + δ • response gap) lifted
  exact (congrArg₂ (fun a b : BurnolPaAmbientCarrier => a + δ • b) old next).trans
    (balance.trans correction)

end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
