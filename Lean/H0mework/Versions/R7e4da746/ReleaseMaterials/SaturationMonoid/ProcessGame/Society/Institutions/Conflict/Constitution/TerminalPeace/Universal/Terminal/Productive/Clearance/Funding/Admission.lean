import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Funding.Native
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Shared
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Publication

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable normalise)
open Quantities.Execution
open Reparation.Actual (ReceiptAnswers Script)
open private authorized_inventory_is_the_physical_inventory from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "RawWord" => RawEvent Party Good Port Technology Instrument

abbrev nativeCheckInput (source : C) := Public.Scope.checkInput source.native.input

abbrev nativeScope (source : C) (word : RawWord) :=
  Public.Scope.scope source.native.input source.native.depth source.native.count source.native.prefixLimit
    source.native.renewalLimit source.native.oldPast source.native.actual.snapshot word

abbrev nativeOrigin (source : C) :=
  Capitalism.Universal.Abolition.Root.Actual.origin source.native.input source.native.depth source.native.count

/-- The legacy native guard can require a larger opening need floor and a
literal whole-bundle payment, while the material check reads paid totals. -/
structure FundingChecks (source : C) (origin : Raw) (roster : List Party) (word : RawWord) : Prop where
  original : ∀ cell ∈ originalRequirements (nativeCheckInput source) (nativeOrigin source) (nativeScope source word),
    cell ∈ originalRequirements source.native.input origin roster
  bundles : Capitalism.Universal.Exit.Necessity.AllNeedsPaid (nativeCheckInput source).law
    source.raw (nativeScope source word) word

namespace Funding

variable (source : Conflict.Root.Cut Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (word : RawEvent Party Good Port Technology Instrument)

private theorem literal_of_paid (paid : Supply.Period source.native.input origin source.raw roster word) :
    normalise word = word := by
  unfold normalise
  conv => rhs; rw [← List.map_id word]
  apply List.map_congr_left
  intro request listed
  have original : request ∈ (source.native.input.law.rawItems source.raw word).map ExecutionItem.request := by
    rwa [RawLaw.rawItems, RawLaw.inventory_requests_exact]
  obtain ⟨item, present, rfl⟩ := List.mem_map.mp original
  exact Request.resign_self _ (paid.own item present).noConsent

private theorem physical_execution (paid : Supply.Period source.native.input origin source.raw roster word) :
    (nativeCheckInput source).law.execute source.raw 0 word = source.native.input.law.execute source.raw 0 word :=
  authorized_inventory_is_the_physical_inventory source.native.input source.raw word 0
    (fun item original => (paid.own item original).valid)

private theorem physical_items (paid : Supply.Period source.native.input origin source.raw roster word) :
    (nativeCheckInput source).law.rawItems source.raw word = source.native.input.law.rawItems source.raw word :=
  congrArg ExecutionResult.items (physical_execution source origin roster word paid)

private theorem physical_use (paid : Supply.Period source.native.input origin source.raw roster word)
    (person : Party) (purpose : Use) (good : Good) :
    actualUse (nativeCheckInput source) source.raw word person purpose good =
      actualUse source.native.input source.raw word person purpose good := by
  unfold actualUse
  rw [physical_items source origin roster word paid]
  apply congrArg List.sum
  apply List.map_congr_left
  intro item listed
  have legal := (paid.own item listed).valid
  have publicLegal : (nativeCheckInput source).law.Valid item.before item.request :=
    PublicFunction.valid_physical _ _ _ legal
  have debit : (nativeCheckInput source).law.actualDebit item.before item.request =
      source.native.input.law.actualDebit item.before item.request := by
    simp only [RawLaw.actualDebit, if_pos legal, if_pos publicLegal]
    rfl
  rw [debit]

private theorem physical_period (paid : Supply.Period source.native.input origin source.raw roster word) :
    Supply.Period (nativeCheckInput source) origin source.raw roster word := by
  refine ⟨?_, ?_, ?_, paid.positiveClock⟩
  · intro item listed
    rw [physical_items source origin roster word paid] at listed
    have original := paid.own item listed
    exact ⟨original.operation, original.member, original.noConsent, PublicFunction.valid_physical _ _ _ original.valid⟩
  · intro cell original
    rw [physical_use source origin roster word paid]
    exact paid.originalFloor cell original
  · intro cell original
    rw [physical_use source origin roster word paid]
    exact paid.currentFloor cell original

/-- A checked original period supplies all remaining native guards
through its literal physical inventory. -/
theorem source_period_checks (paid : Supply.Period source.native.input origin source.raw roster word)
    (guards : FundingChecks source origin roster word) :
    Quantities.Execution.PeriodChecks source word := by
  unfold Quantities.Execution.PeriodChecks Public.Scope.Checks
  rw [literal_of_paid source origin roster word paid]
  have stable := paid.stable_word
  have own := physical_period source origin roster word paid
  refine ⟨fun request listed => (stable request listed).1, ?_, own.toActualAndIndependent, guards.bundles,
    sharedRequiredPorts_noFreshControl (nativeCheckInput source) source.raw word (fun _ _ _ _ _ => rfl), ?_, trivial⟩
  · intro cell original
    change cell.2.2.2 ≤ actualUse (nativeCheckInput source) source.raw word cell.1 cell.2.1 cell.2.2.1
    rw [physical_use source origin roster word paid]
    exact paid.originalFloor cell (guards.original cell original)
  · intro person _
    have same : ((nativeCheckInput source).law.next source.raw word).technology = source.raw.technology :=
      (Balance.stable_execution_coordinates (nativeCheckInput source).law source.raw 0 word stable).2.1
    change TechniqueDominates ((nativeCheckInput source).law.technique source.raw.technology person)
      ((nativeCheckInput source).law.technique ((nativeCheckInput source).law.next source.raw word).technology person)
    rw [same]
    exact ⟨fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

theorem paid_body_reads_the_original_execution
    (ready : Ready source) (review : ReviewAvailable source)
    (paid : Supply.Period source.native.input origin source.raw roster word)
    (guards : FundingChecks source origin roster word) :
    (next source (some (.execute word))).raw = source.native.input.law.next source.raw word ∧
      Boundary.Actual.items source (some (.execute word)) = source.native.input.law.rawItems source.raw word := by
  have checked := source_period_checks source origin roster word paid guards
  have literal := literal_of_paid source origin roster word paid
  refine ⟨?_, ?_⟩
  · rw [a_checked_period_has_the_original_real_effect source word ready review checked, literal]
    change (nativeCheckInput source).law.next source.raw word = _
    unfold RawLaw.next
    rw [physical_execution source origin roster word paid]
    rfl
  · change inventory source [some (.execute word)] = _
    rw [a_checked_period_has_the_original_paid_inventory source word ready review checked, literal]
    exact physical_items source origin roster word paid

end Funding

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
