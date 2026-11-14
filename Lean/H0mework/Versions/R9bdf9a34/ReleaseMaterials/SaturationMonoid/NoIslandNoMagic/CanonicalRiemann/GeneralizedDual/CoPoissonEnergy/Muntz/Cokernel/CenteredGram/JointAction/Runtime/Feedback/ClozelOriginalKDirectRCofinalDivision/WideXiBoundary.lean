import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiAdjointStock

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact

open BurnolPhysicalState Filter
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
attribute [local instance] DivisionEffectPrice.wideNormed

open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
open private native_read from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiAdjointStock

local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "J" => fun c : BurnolCompletedMellinCoordinate => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "Resolvent" => burnolDirectRightResolventCLM

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "stock" => actualWide observation nontrivial half depth
local notation "literal" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "settled" => paid observation nontrivial half depth ordinal
local notation "A" => advanceWide c observation.mathlibZero

private theorem double_zero : riemannZeta (C a).value = 0 := by
  rw [BoundaryXiSlot.conjugate_twice c]
  exact observation.mathlibZero

theorem literal_contact : stock ordinal ∈ contact a degree := by
  apply (contact_iff a degree _).mpr
  intro i within
  have source := (BoundaryXiSlot.actual_slot observation nontrivial half depth ordinal).1 i within
  have same : ThreePortCausal.field observation nontrivial half depth ordinal 0 = raw ordinal := by
    rw [ThreePortCausal.actual_field, Nat.add_zero]
  rw [same] at source
  rw [BoundaryXiSlot.conjugate_twice c]
  exact source

private def positionOf (value : Wide) : PositionField :=
  ⟨readField value, LogStock.field_mem (base (toWhole value))⟩

def terminalPosition (x : contact a degree) : PositionField :=
  positionOf (terminal a (double_zero observation half) degree x)

theorem terminal_original :
    terminalPosition observation half
      ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩ = literal ordinal := by
  apply Subtype.ext
  have terminalRaw := terminal_field a (double_zero observation half) degree
    (⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩ : contact a degree)
  change _ = BoundaryXiSlot.slot observation nontrivial half depth ordinal
  unfold BoundaryXiSlot.slot
  rw [ThreePortCausal.actual_field, Nat.add_zero]
  exact terminalRaw

private def terminalFieldMap : contact a degree →L[ℂ] BurnolL2 :=
  (((J a)^degree) : BurnolL2 →L[ℂ] BurnolL2).comp
    (readField.comp (contact a degree).subtypeL)

def terminalPositionMap : contact a degree →L[ℂ] PositionField :=
  (terminalFieldMap observation half).codRestrict PositionField fun x => by
    have source := terminal_field a (double_zero observation half) degree x
    rw [show terminalFieldMap observation half x = _ from source.symm]
    exact (terminalPosition observation half x).property

theorem terminal_map_source (x : contact a degree) :
    terminalPositionMap observation half x = terminalPosition observation half x :=
  Subtype.ext (terminal_field a (double_zero observation half) degree x).symm

/-- Read the exact paid current with its full low-Xi contact projection and retained difference. -/
def paidQualified (n m : Nat) : contact a degree := qualify a degree (settled n m).2.1

attribute [local irreducible] paid currentFit actualWide errorBudget in
theorem paid_qualification_error (n m : Nat) :
    ‖(paidQualified observation nontrivial half depth ordinal n m : Wide) - stock ordinal‖ ≤
      errorBudget observation nontrivial half depth ordinal n m ∧
    ‖rejected a degree (settled n m).2.1‖ ≤ errorBudget observation nontrivial half depth ordinal n m := by
  let x := (settled n m).2.1
  let y : contact a degree := ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩
  have current : x = currentFit observation nontrivial half depth ordinal n m :=
    congrArg (fun t : Wide × Wide × Wide => t.2.1) (paid_source observation nontrivial half depth ordinal n m)
  have fit := finite_graph_error observation nontrivial half depth ordinal n m
  have measured : ‖x-(y : Wide)‖ ≤ errorBudget observation nontrivial half depth ordinal n m :=
    (congrArg (fun t : Wide => ‖t-(y : Wide)‖) current).trans_le fit
  have cost := qualification_cost a degree x y
  exact ⟨cost.1.trans measured,cost.2.trans measured⟩

attribute [local irreducible] paid currentFit in
/-- The actual original R write advances the qualified entire stock and its independent difference. -/
theorem qualified_paid_next (n m : Nat) :
    let x := paidQualified observation nontrivial half depth ordinal n m
    let before := (settled n m).2.1
    let after := (settled n m).2.2
    A (x : Wide) ∈ contact a degree ∧
    after = A (x : Wide) + A (rejected a degree before) := by
  let x := paidQualified observation nontrivial half depth ordinal n m
  let before := (settled n m).2.1
  let after := (settled n m).2.2
  have advance : after = A before := by
    have actual := paid_source observation nontrivial half depth ordinal n m
    exact (congrArg (fun row : Wide × Wide × Wide => row.2.2) actual).trans
      (congrArg (fun row : Wide × Wide × Wide => A row.2.1) actual).symm
  have split := qualify_split a degree before
  have membership : A (x : Wide) ∈ contact a degree :=
    forward_contact a c (double_zero observation half) observation.mathlibZero degree x
  have write : A ((x : Wide) + rejected a degree before) =
      A (x : Wide) + A (rejected a degree before) :=
    map_add A (x : Wide) (rejected a degree before)
  exact ⟨membership, advance.trans ((congrArg A split).symm.trans write)⟩

attribute [local irreducible] paid actualWide in
theorem paid_terminal_tendsto :
    Tendsto (fun n => terminalPosition observation half
      (paidQualified observation nontrivial half depth ordinal n n)) atTop (𝓝 (literal ordinal)) := by
  let projection := qualify a degree
  let measured := terminalPositionMap observation half
  let original : contact a degree := ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩
  have recovered := ((measured.comp projection).continuous.tendsto (stock ordinal)).comp
    (actual_graph_tendsto observation nontrivial half depth ordinal)
  have projected : projection (stock ordinal) = original :=
    qualify_self a degree original
  have limit : (measured.comp projection) (stock ordinal) = literal ordinal :=
    (congrArg measured projected).trans ((terminal_map_source observation half original).trans
      (terminal_original observation nontrivial half depth ordinal))
  have result := (congrArg (fun value : PositionField => Tendsto
    (fun n : Nat => (measured.comp projection) (settled n n).2.1) atTop (𝓝 value)) limit).mp recovered
  exact result.congr' (Eventually.of_forall fun n => terminal_map_source observation half
    (paidQualified observation nontrivial half depth ordinal n n))

end WideResidualReturn.XiContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
