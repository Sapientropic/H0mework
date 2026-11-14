import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FirstPaReturn
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PriceLiteralOccurrence

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.AdjointCofinalReturn

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock
open HilbertInventory.SecondConductorStock.SingleSlot
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKDirectRCofinalReentrySourceAction
open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (sourceIndex)
open scoped InnerProductSpace

open private fullRead from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
open private adjoint_R adjoint_powers_R from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "R" => burnolDirectRightResolventCLM c
local notation "J" => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKCombCofinalPaAction.Q
local notation "invisible" => OriginalKCombCofinalPaAction.invisible
local notation "V" => (sourceReentryVector c : BurnolPaAmbientCarrier)
local notation "u" => fourierL2 (burnolUnitTailResponse barC 4)
local notation "k" => FirstPaReturn.exitIndex observation nontrivial half
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "advance" => DivisionPriceStream.advance observation nontrivial half depth

private def adjointWord : BurnolL2 →L[ℂ] BurnolL2 := (J).comp (J^(k-1))
local notation "word" => adjointWord observation nontrivial half

private theorem word_commutes (value : BurnolL2) : word (R value) = R (word value) := by
  change J ((J^(k-1)) (R value)) = R (J ((J^(k-1)) value))
  rw [adjoint_powers_R, adjoint_R]

private theorem word_powers (value : BurnolL2) (n : Nat) :
    word ((R^n) value) = (R^n) (word value) := by
  induction n with
  | zero => simp only [pow_zero,one_apply_eq_self]
  | succ n prior => rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,word_commutes,prior]

/-- The adjoint face is generated from the complete price-decoded field of the original row. -/
def face (data : Data) : BurnolL2 := word (fullRead (graph data : Ambient))
local notation "currentFace" => face observation nontrivial half depth

private def betaRead : BurnolL2 →L[ℂ] ℂ :=
  (innerSL ℂ u).comp ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp Q)

local notation "β" => betaRead observation half

private theorem raw_power (ordinal : Nat) : raw ordinal = (R^(sourceIndex observation ordinal)) seed := by
  have direct : OriginalKCombPhysicalAction.R observation nontrivial half = R :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source,direct,← ContinuousLinearMap.toLinearMap_pow]
  rfl

theorem face_actual (ordinal : Nat) : currentFace (capture (stock ordinal)) = word (raw ordinal) := by
  unfold face
  rw [DivisionPriceStream.graph_capture]
  rfl

private theorem raw_next (data : Data) :
    fullRead (graph (advance data) : Ambient) = R (fullRead (graph data : Ambient)) := by
  have written : graph (advance data) = advanceWide c observation.mathlibZero (graph data) :=
    congrArg Prod.fst (DivisionPriceStream.exact_write observation nontrivial half depth data)
  have actual := congrArg (fun x : Wide => fullRead (x : Ambient)) written
  change fullRead (graph (advance data) : Ambient) = R (fullRead (graph data : Ambient)) at actual
  exact actual

theorem face_next (data : Data) : currentFace (advance data) = R (currentFace data) := by
  unfold face
  rw [raw_next,word_commutes]

include nontrivial in
private theorem fibre_return (value : BurnolL2) : E (R (invisible value)) = β value • V := by
  change E (burnolDirectRightResolvent ((c).value/2) (invisible value)) = β value • V
  rw [full_invisible_reentry]
  change inner ℂ u (invisible value) • V = inner ℂ u (Q value : BurnolL2) • V
  rw [source_unit_invisible_pair_Q observation nontrivial half.down]

/-- Both the adjoint face and its true rank-one Pa return use the same native next write. -/
theorem face_write (data : Data) :
    E (currentFace (advance data)) - E (R (E (currentFace data) : BurnolL2)) =
      β (currentFace data) • V := by
  rw [face_next,← map_sub E,← map_sub (R)]
  exact fibre_return observation nontrivial half _

private theorem anchor_return : β (word seed) • V ≠ 0 := by
  have returnEq := fibre_return observation nontrivial half (word seed)
  have sourceEq : E (R (invisible (word seed))) =
      FirstPaReturn.returned observation nontrivial half := by
    unfold FirstPaReturn.returned
    rw [OriginalKCombCofinalRAction.original_R_direct]
    rfl
  rw [← returnEq, sourceEq]
  exact FirstPaReturn.return_nonzero observation nontrivial half

include nontrivial in
private theorem vector_ne : V ≠ 0 := by
  intro erased
  exact anchor_return observation nontrivial half (by rw [erased,smul_zero])

private theorem anchor_beta_ne : β (word seed) ≠ 0 := by
  intro erased
  exact anchor_return observation nontrivial half (by rw [erased,zero_smul])

/-- Every literal cofinal tail contains a nonzero return of this actual adjoint face. -/
theorem tail_return (start : Nat) :
    ∃ ordinal > start, β (currentFace (capture (stock ordinal))) ≠ 0 := by
  by_contra! silent
  let cutoff := sourceIndex observation (start+1)
  have quiet (n : Nat) (late : cutoff ≤ n) : β ((R^n) (word seed)) = 0 := by
    let ordinal := n-(sourceIndex observation 0)
    have address : sourceIndex observation ordinal = n := by
      dsimp [cutoff,ordinal,sourceIndex] at *
      omega
    have later : start < ordinal := by
      dsimp [cutoff,ordinal,sourceIndex] at *
      omega
    have price := silent ordinal later
    rw [face_actual, raw_power, word_powers, address] at price
    exact price
  have zero := original_power_read_zero_of_tail (β) c (word seed) cutoff quiet 0
  rw [pow_zero,one_apply_eq_self] at zero
  exact anchor_beta_ne observation nontrivial half zero

local notation "received" => PriceLiteralOccurrence.readPacket observation nontrivial half depth

/-- The actual old native receipt's whole branch generates the same adjoint face as the independent next price stream. -/
theorem receipt_face (ordinal : Nat) :
    let data := capture (stock ordinal)
    word (PacketFit.packetWhole (received data)) = currentFace (advance data) := by
  let data := capture (stock ordinal)
  have whole : PacketFit.packetWhole (received data) = fullRead (graph (advance data) : Ambient) :=
    (PriceLiteralOccurrence.actual_native_next observation nontrivial half depth ordinal).2
  exact congrArg (fun value : BurnolL2 => word value) whole

/-- One retained original K price detects the actual adjoint return in every cofinal tail. -/
theorem retained_price_each_tail :
    ∃ i : Nat, ∀ start : Nat, ∃ ordinal > start,
      let data := capture (stock ordinal)
      PhysicalPriceCountable.price (DenseDivisionPrice.height observation nontrivial half depth i)
        (E (word (PacketFit.packetWhole (received data))) -
          E (R (E (currentFace data) : BurnolL2))) ≠ 0 := by
  have witness : ∃ i : Nat, PhysicalPriceCountable.price
      (DenseDivisionPrice.height observation nontrivial half depth i) V ≠ 0 := by
    by_contra! quiet
    exact vector_ne observation nontrivial half
      (DenseDivisionPrice.separates observation nontrivial half depth V quiet)
  obtain ⟨i,visible⟩ := witness
  refine ⟨i,fun start => ?_⟩
  obtain ⟨ordinal,later,live⟩ := tail_return observation nontrivial half depth start
  refine ⟨ordinal,later,?_⟩
  dsimp only
  rw [receipt_face observation nontrivial half depth ordinal,face_write]
  have changed := mul_ne_zero live visible
  exact fun erased => changed (by
    unfold PhysicalPriceCountable.price at erased ⊢
    rwa [map_smul,smul_eq_mul] at erased)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.AdjointCofinalReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
