import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Registered

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual (Script)
open Quantities.Execution (endAt)
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

/-- A local production proposal contains the recipe and the work offered
for it. The original parties answer on separate lanes. -/
structure ProductionOffer (Party Good Port Technology Instrument : Type) where
  technique : Technology → Party → Technique Good Port
  pilot : RawEvent Party Good Port Technology Instrument
  attempts : RawEvent Party Good Port Technology Instrument

structure ProductionMenu (Party Good Port Technology Instrument : Type) where
  proposals : List (ProductionOffer Party Good Port Technology Instrument)
  replies : Script Party Good Port Technology Instrument → Fin proposals.length → Party → Bool

def ProductionMenu.empty : ProductionMenu Party Good Port Technology Instrument :=
  ⟨[], fun _ i _ => Fin.elim0 i⟩

abbrev ProductionChoice (menu : ProductionMenu Party Good Port Technology Instrument) :=
  Option (Fin menu.proposals.length)

variable (seed : Conflict.Root.Cut Party Good Port Technology Instrument)
  {community : Party → Community}
  {offers : ProductionMenu Party Good Port Technology Instrument}

/-- A finite original prefix can consume pending work and reach the
existing native review gate before living service starts. -/
def ReadyEntry {seed : Conflict.Root.Cut Party Good Port Technology Instrument}
    (loss : Reparation.Actual.Occurrence seed community) (word : Script Party Good Port Technology Instrument) : Prop :=
  let cut := endAt seed (Occurrence.history loss ++ word)
  Ready cut ∧ ReviewAvailable cut

private def amendProduction (offer : ProductionOffer Party Good Port Technology Instrument) :
    ProgrammeSource.Input Party Good Port Technology Instrument :=
  { seed.native.input with
    law := { seed.native.input.law with technique := offer.technique }
    localAttempts := fun raw => seed.native.input.localAttempts raw ++ (offer.pilot ++ offer.attempts) }

/-- A production change also pays the people who have acquired standing
on the accepted prefix. Inherited production keeps its original scope. -/
noncomputable def productionRoster (loss : Reparation.Actual.Occurrence seed community)
    (word : Script Party Good Port Technology Instrument) (choice : ProductionChoice offers) : List Party :=
  match choice with
  | none => originalBearers loss
  | some _ =>
    (originalBearers loss ++ ExposureGuard.bearers seed community (Occurrence.history loss ++ word)).dedup

theorem production_roster_keeps_original_bearers
    (loss : Reparation.Actual.Occurrence seed community) (word : Script Party Good Port Technology Instrument)
    (choice : ProductionChoice offers) {person : Party} (original : person ∈ originalBearers loss) :
    person ∈ productionRoster seed loss word choice := by
  cases choice with
  | none => exact original
  | some index => exact List.mem_dedup.mpr (List.mem_append_left _ original)

/-- The existing residents and the original exposure holders answer at
the exact installation cut. These answers do not act as debt receipts. -/
def ProductionApproved (loss : Reparation.Actual.Occurrence seed community)
    (word : Script Party Good Port Technology Instrument) (choice : ProductionChoice offers) : Prop :=
  match choice with
  | none => True
  | some i =>
    let past := Occurrence.history loss ++ word
    ∀ person ∈ productionRoster seed loss word (some i), offers.replies past i person = true

/-- An amended recipe is first used in its submitted material experiment.
The experiment is part of the actual paid history. -/
def ProductionStartsWith (choice : ProductionChoice offers)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  match choice with
  | none => True
  | some i => word = offers.proposals[i].pilot ∧
    ∃ request ∈ word, ∃ person, request.operation = .produce person

variable (loss : Reparation.Actual.Occurrence seed community)
  (word : Script Party Good Port Technology Instrument)

/-- Only the exact ready, reviewable and personally authorized cut
can supply a different recipe to the material interpreter. -/
noncomputable def productionInput (choice : ProductionChoice offers) :
    ProgrammeSource.Input Party Good Port Technology Instrument := by
  classical
  exact match choice with
  | none => seed.native.input
  | some i =>
    if ReadyEntry loss word ∧ ProductionApproved seed loss word (some i) then
      amendProduction seed offers.proposals[i]
    else seed.native.input

theorem production_at_an_authorized_cut (index : Fin offers.proposals.length)
    (ready : ReadyEntry loss word) (approved : ProductionApproved seed loss word (some index)) :
    productionInput seed loss word (some index) =
      { seed.native.input with
        law := { seed.native.input.law with technique := offers.proposals[index].technique }
        localAttempts := fun raw => seed.native.input.localAttempts raw ++
          (offers.proposals[index].pilot ++ offers.proposals[index].attempts) } := by
  classical
  unfold productionInput
  exact if_pos ⟨ready, approved⟩

theorem production_without_authority_reads_the_old_programme (choice : ProductionChoice offers)
    (denied : ¬ (ReadyEntry loss word ∧ ProductionApproved seed loss word choice)) :
    productionInput seed loss word choice = seed.native.input := by
  classical
  cases choice with
  | none => rfl
  | some i =>
    unfold productionInput
    exact if_neg denied

theorem production_preserves_need_and_clock_laws (choice : ProductionChoice offers) :
    (productionInput seed loss word choice).law.necessities = seed.native.input.law.necessities ∧
    (productionInput seed loss word choice).law.mandatoryMaintenance = seed.native.input.law.mandatoryMaintenance ∧
    (productionInput seed loss word choice).law.duration = seed.native.input.law.duration := by
  classical
  cases choice with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some i =>
    simp only [productionInput]
    split <;> exact ⟨rfl, rfl, rfl⟩

theorem production_preserves_policy_and_financial_terms (choice : ProductionChoice offers) :
    (productionInput seed loss word choice).law.policy = seed.native.input.law.policy ∧
    (productionInput seed loss word choice).law.stockPort = seed.native.input.law.stockPort ∧
    (productionInput seed loss word choice).law.settlementUnit = seed.native.input.law.settlementUnit ∧
    (productionInput seed loss word choice).law.settlementRate = seed.native.input.law.settlementRate := by
  classical
  cases choice with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some i =>
    simp only [productionInput]
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
