import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideReturnFinalPayment
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 150000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState Filter
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology InnerProductSpace

open private fullRead from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
open private adjointWord word_commutes from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn

namespace Pa
export OriginalKCombCofinalPaAction (E invisible)
export OriginalKDirectRCofinalReentrySourceAction (sourceReentryAction full_invisible_reentry)
end Pa

local notation "Resolvent" => burnolDirectRightResolventCLM

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "native" => advanceWide c observation.mathlibZero
local notation "word" => adjointWord observation nontrivial half
local notation "source" => paid observation nontrivial half depth ordinal
local notation "stock" => actualWide observation nontrivial half depth
private def readField : Wide →L[ℂ] BurnolL2 := fullRead.comp unitGap.subtypeL
local notation "line" => DenseDivisionPrice.height observation nontrivial half depth

def paReturn (n m : Nat) : BurnolPaAmbientCarrier :=
  let actual := source n m
  Pa.E (word (readField actual.2.2)) -
    Pa.E (Resolvent c (Pa.E (word (readField actual.2.1)) : BurnolL2))

theorem field_next (n m : Nat) :
    readField (source n m).2.2 = Resolvent c (readField (source n m).2.1) := by
  let previous := (source n m).2.1
  have executed := paid_source observation nontrivial half depth ordinal n m
  have exactNext : (source n m).2.2 = native previous :=
    (congrArg (fun value : Wide × Wide × Wide => value.2.2) executed).trans
      (congrArg (fun value : Wide × Wide × Wide => native value.2.1) executed).symm
  have written : readField (source n m).2.2 = readField (native previous) :=
    congrArg readField exactNext
  have reads (z : Wide) : readField (native z) = Resolvent c (readField z) :=
    advance_raw c observation.mathlibZero (toWhole z)
  exact written.trans (reads previous)

/-- The two actual terminal fields write the complete original rank-one Pa return. -/
theorem pa_return_eq (n m : Nat) :
    paReturn observation nontrivial half depth ordinal n m =
      Pa.sourceReentryAction c (Pa.invisible (word (readField (source n m).2.1))) := by
  let old := word (readField (source n m).2.1)
  have arrived : word (readField (source n m).2.2) = Resolvent c old :=
    (congrArg word (field_next observation nontrivial half depth ordinal n m)).trans
      (word_commutes observation nontrivial half _)
  have difference : Pa.E (word (readField (source n m).2.2)) -
      Pa.E (Resolvent c (Pa.E old : BurnolL2)) =
      Pa.E (Resolvent c (Pa.invisible old)) := by
    calc
      _ = Pa.E (Resolvent c old) - Pa.E (Resolvent c (Pa.E old : BurnolL2)) :=
        congrArg (fun value => Pa.E value-Pa.E (Resolvent c (Pa.E old : BurnolL2))) arrived
      _ = Pa.E (Resolvent c (Pa.invisible old)) := by
        unfold Pa.invisible
        rw [map_sub, map_sub]
  exact difference.trans (Pa.full_invisible_reentry c old)

private def limitReturn : BurnolPaAmbientCarrier :=
  Pa.E (word (readField (stock (ordinal+1)))) -
    Pa.E (Resolvent c (Pa.E (word (readField (stock ordinal))) : BurnolL2))

theorem pa_return_tendsto :
    Tendsto (fun n => paReturn observation nontrivial half depth ordinal n n) atTop
      (𝓝 (limitReturn observation nontrivial half depth ordinal)) := by
  let forward : Wide →L[ℂ] BurnolPaAmbientCarrier := Pa.E.comp ((word).comp readField)
  let into : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  let self := (Pa.E.comp ((Resolvent c).comp into)).comp forward
  have full := (forward.continuous.tendsto _).comp
    (actual_next_graph observation nontrivial half depth ordinal)
  have known := (self.continuous.tendsto _).comp
    (actual_graph_tendsto observation nontrivial half depth ordinal)
  exact full.sub known

/-- One original K address detects finite paid Pa returns arbitrarily far along the literal source. -/
theorem actual_finite_pa_return_visible :
    ∃ i : Nat, ∀ start : Nat, ∃ j > start,
      ∀ᶠ n : Nat in atTop, PhysicalPriceCountable.price (line i)
        (paReturn observation nontrivial half depth j n n) ≠ 0 := by
  obtain ⟨i, detects⟩ := AdjointCofinalReturn.retained_price_each_tail observation nontrivial half depth
  refine ⟨i, fun start => ?_⟩
  obtain ⟨j, later, seen⟩ := detects start
  refine ⟨j, later, ?_⟩
  let test := PhysicalPriceCountable.price (line i)
  let current := PriceStream.capture observation nontrivial half depth (stock j)
  let raw := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
  have before : AdjointCofinalReturn.face observation nontrivial half depth current =
      word (readField (stock j)) := by
    have literal : readField (stock j) = raw j := rfl
    exact (AdjointCofinalReturn.face_actual observation nontrivial half depth j).trans
      (congrArg word literal.symm)
  have born := AdjointCofinalReturn.receipt_face observation nontrivial half depth j
  have wrote : AdjointCofinalReturn.face observation nontrivial half depth
      (PriceStream.advance observation nontrivial half depth current) =
      word (readField (stock (j+1))) := by
    have literal := (DivisionPriceStream.actual_current_and_next observation nontrivial half depth j).2.2.1
    have moved := congrArg (AdjointCofinalReturn.face observation nontrivial half depth) literal
    have rawNext : readField (stock (j+1)) = raw (j+1) := rfl
    exact moved.trans ((AdjointCofinalReturn.face_actual observation nontrivial half depth (j+1)).trans
      (congrArg word rawNext.symm))
  have limitLive : test (limitReturn observation nontrivial half depth j) ≠ 0 := by
    dsimp only at seen
    have equal := congrArg₂ (fun next old : BurnolL2 =>
      test (Pa.E next-Pa.E (Resolvent c (Pa.E old : BurnolL2)))) (born.trans wrote) before
    have correct : test (limitReturn observation nontrivial half depth j) ≠ 0 :=
      fun erased => seen (equal.trans erased)
    exact correct
  have measured := (test.continuous.tendsto _).comp (pa_return_tendsto observation nontrivial half depth j)
  exact measured.eventually_ne limitLive

end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
