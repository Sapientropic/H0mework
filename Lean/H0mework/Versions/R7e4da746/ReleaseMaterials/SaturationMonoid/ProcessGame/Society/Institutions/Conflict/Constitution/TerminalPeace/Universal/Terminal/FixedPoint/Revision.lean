import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Productivity
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Production

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (inspectList)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

variable {Party Good Port Technology Instrument : Type}

local notation "Input" => ProgrammeSource.Input Party Good Port Technology Instrument
local notation "Offer" => ProductionOffer Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

/-- Keep the original public law and add only the proposed technique and
its submitted instructions to the original local attempts. -/
def reviseProgramme (old : Input) (offer : Offer) : Input :=
  { old with
    law := { old.law with technique := offer.technique }
    localAttempts := fun raw => old.localAttempts raw ++ (offer.pilot ++ offer.attempts) }

/-- Revisions may change the production table and the local attempt
alphabet. All remaining registered terms keep their original source. -/
def KeepsPublicTerms (first current : Input) : Prop :=
  current =
    { first with
      law := { first.law with technique := current.law.technique }
      localAttempts := current.localAttempts }

theorem KeepsPublicTerms.refl (input : Input) : KeepsPublicTerms input input :=
  rfl

theorem KeepsPublicTerms.trans {first middle current : Input}
    (earlier : KeepsPublicTerms first middle) (later : KeepsPublicTerms middle current) :
    KeepsPublicTerms first current := by
  unfold KeepsPublicTerms at earlier later ⊢
  calc
    current = _ := later
    _ = _ := congrArg (fun input : Input =>
      { input with
        law := { input.law with technique := current.law.technique }
        localAttempts := current.localAttempts }) earlier

theorem reviseProgramme_keeps_public_terms (old : Input) (offer : Offer) :
    KeepsPublicTerms old (reviseProgramme old offer) :=
  rfl

theorem revision_preserves_need_and_clock_laws (old : Input) (offer : Offer) :
    (reviseProgramme old offer).law.necessities = old.law.necessities ∧
      (reviseProgramme old offer).law.mandatoryMaintenance = old.law.mandatoryMaintenance ∧
      (reviseProgramme old offer).law.duration = old.law.duration :=
  ⟨rfl, rfl, rfl⟩

theorem revision_preserves_policy_and_control (old : Input) (offer : Offer) :
    (reviseProgramme old offer).law.policy = old.law.policy ∧
      (reviseProgramme old offer).law.controller = old.law.controller ∧
      (reviseProgramme old offer).law.allowed = old.law.allowed ∧
      (reviseProgramme old offer).law.stockPort = old.law.stockPort ∧
      (reviseProgramme old offer).law.revisionPort = old.law.revisionPort ∧
      (reviseProgramme old offer).law.revisionCost = old.law.revisionCost :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revision_preserves_settlement_terms (old : Input) (offer : Offer) :
    (reviseProgramme old offer).law.settlementUnit = old.law.settlementUnit ∧
      (reviseProgramme old offer).law.settlementRate = old.law.settlementRate ∧
      (reviseProgramme old offer).law.issuerPort = old.law.issuerPort :=
  ⟨rfl, rfl, rfl⟩

/-- Each approval is read at the actual erased resident and current
physical opening. The proposal carries no answers. -/
abbrev RevisionAnswers (Party Good Port Technology Instrument : Type) :=
  AnyAuthoritativeRootCurrent.{0} → RawCurrent Party Good Technology Instrument →
    ProductionOffer Party Good Port Technology Instrument → Party → Bool

def RevisionApproval (answers : RevisionAnswers Party Good Port Technology Instrument)
    (resident : AnyAuthoritativeRootCurrent.{0}) (raw : Raw) (roster : List Party) (offer : Offer) : Prop :=
  ∀ person ∈ roster, answers resident raw offer person = true

theorem revision_registers_its_pilot (old : Input) (offer : Offer) (raw : Raw) :
    Supply.Registered (reviseProgramme old offer) raw offer.pilot := by
  intro request listed
  change request ∈ (old.localAttempts raw ++ (offer.pilot ++ offer.attempts)) ++ ProgrammeSource.wordAt old raw
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ listed))

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- The submitted experiment is the actual checked productive period. -/
structure RevisionKit (old : Input) (origin : Raw) (roster : List Party) (base : Raw) (quantum : ℚ) (offer : Offer) where
  recipe : Recipe (reviseProgramme old offer) origin roster base quantum
  starts : recipe.move.word = offer.pilot
  produces : ∃ request ∈ offer.pilot, ∃ person, request.operation = .produce person

namespace RevisionKit

variable {old : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin base : RawCurrent Party Good Technology Instrument} {roster : List Party} {quantum : ℚ}
  {offer : ProductionOffer Party Good Port Technology Instrument}
  (kit : RevisionKit old origin roster base quantum offer)

theorem at_opening (raw : Raw) (safe : InReserve base raw) :
    (kit.recipe.moveAt raw safe).word = offer.pilot :=
  (kit.recipe.moveAt_word raw safe).trans kit.starts

end RevisionKit

variable (old : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (base : RawCurrent Party Good Technology Instrument) (quantum : ℚ)
  (answers : RevisionAnswers Party Good Port Technology Instrument)
  (resident : AnyAuthoritativeRootCurrent.{0}) (raw : RawCurrent Party Good Technology Instrument)
  (offer : ProductionOffer Party Good Port Technology Instrument)

inductive RevisionDecision where
  | checked (kit : RevisionKit old origin roster base quantum offer)
      (approved : RevisionApproval answers resident raw roster offer)
  | refused (person : Party) (listed : person ∈ roster) (withheld : answers resident raw offer person = false)
  | unproductive (approved : RevisionApproval answers resident raw roster offer)
      (excluded : ¬ Nonempty (RevisionKit old origin roster base quantum offer))

/-- The original independent replies are checked before the proposed
recipe's paid period and reusable reserve law are selected. -/
noncomputable def inspectRevision : RevisionDecision old origin roster base quantum answers resident raw offer :=
  match inspectList (fun person => answers resident raw offer person = true) roster with
  | .failure person listed no => .refused person listed (Bool.eq_false_of_not_eq_true no)
  | .clear approved => by
    classical
    by_cases available : Nonempty (RevisionKit old origin roster base quantum offer)
    · exact .checked (Classical.choice available) approved
    · exact .unproductive approved available

theorem inspectRevision_passes_iff :
    (∃ kit approved, inspectRevision old origin roster base quantum answers resident raw offer = .checked kit approved) ↔
      RevisionApproval answers resident raw roster offer ∧ Nonempty (RevisionKit old origin roster base quantum offer) := by
  constructor
  · rintro ⟨kit, approved, _⟩
    exact ⟨approved, ⟨kit⟩⟩
  · rintro ⟨approved, available⟩
    cases inspectRevision old origin roster base quantum answers resident raw offer with
    | checked kit signed => exact ⟨kit, signed, rfl⟩
    | refused person listed withheld =>
      have impossible : false = true := withheld.symm.trans (approved person listed)
      cases impossible
    | unproductive _ excluded => exact (excluded available).elim

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
