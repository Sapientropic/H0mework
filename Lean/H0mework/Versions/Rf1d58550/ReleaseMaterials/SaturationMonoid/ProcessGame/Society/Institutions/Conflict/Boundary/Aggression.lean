import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Crossings
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Root.Registered
open Space

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Debit" => Row Party Good Port Technology Instrument

abbrev compilerAt (source : C) (word : Word) (community : Party → Community) :=
  crossingCompiler source.native.input.law (source.raw, word) community

abbrev spaceAt (source : C) (word : Word) (community : Party → Community) :=
  sourceCrossings source.native.input.law (source.raw, word) community

abbrev boundaryRow (source : C) (word : Word) (community : Party → Community)
    (boundary : (compilerAt source word community).AnyBoundaryCertificate) : Debit :=
  debitAt source.native.input.law (source.raw, word) boundary.crossing

def BearerAssented (row : Debit) : Prop :=
  row.2.1 = row.1.request.signer ∨ row.2.1 ∈ row.1.request.consents

instance (row : Debit) : Decidable (BearerAssented row) := by
  unfold BearerAssented
  infer_instance

/-- A materially executed boundary capture retains the M11 position, the
foreign loss bearer, and the original whole-ledger execution. -/
structure AggressionAt (source : C) (word : Word) (community : Party → Community) where
  paid : Root.Paid source word
  crossing : (compilerAt source word community).AnyBoundaryCertificate
  listed : crossing ∈ (spaceAt source word community).boundaryCertificates
  unassented : ¬ BearerAssented (boundaryRow source word community crossing)

/-- All unassented losses are read from the generated M11 inventory. -/
def aggressions (source : C) (word : Word) (community : Party → Community)
    (paid : Root.Paid source word) : List (AggressionAt source word community) :=
  (spaceAt source word community).boundaryCertificates.attach.filterMap fun boundary =>
    if unassented : ¬ BearerAssented (boundaryRow source word community boundary.1)
    then some ⟨paid, boundary.1, boundary.2, unassented⟩
    else none

namespace AggressionAt

variable {source : Root.Cut Party Good Port Technology Instrument}
  {word : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community}

abbrev row (attack : AggressionAt source word community) : Debit :=
  boundaryRow source word community attack.crossing

abbrev item (attack : AggressionAt source word community) := attack.row.1

abbrev attacker (attack : AggressionAt source word community) := attack.item.request.signer

abbrev victim (attack : AggressionAt source word community) := attack.row.2.1

abbrev good (attack : AggressionAt source word community) := attack.row.2.2

abbrev quantity (attack : AggressionAt source word community) := loss source.native.input.law attack.row

theorem foreign (attack : AggressionAt source word community) :
    community attack.attacker ≠ community attack.victim :=
  distinct_at_boundary _ _ _ attack.crossing

theorem original (attack : AggressionAt source word community) :
    attack.item ∈ source.native.input.law.rawItems source.raw word ∧
      source.native.input.law.Valid attack.item.before attack.item.request ∧ 0 < attack.quantity := by
  have original := row_at_exact source.native.input.law (source.raw, word)
    attack.crossing.crossing.state attack.row
    (debitAt_mem _ _ attack.crossing.crossing)
  exact ⟨original.1, original.2.1, original.2.2.2.2⟩

def ofPaidBoundary (paid : Root.Paid source word)
    (crossing : (compilerAt source word community).AnyBoundaryCertificate)
    (listed : crossing ∈ (spaceAt source word community).boundaryCertificates) :
    AggressionAt source word community := by
  let row := boundaryRow source word community crossing
  have original := (row_at_exact source.native.input.law (source.raw, word)
    crossing.crossing.state row (debitAt_mem _ _ crossing.crossing)).1
  have request : row.1.request ∈ word := by
    rw [← source.native.input.law.inventory_requests_exact source.raw 0 word]
    exact List.mem_map_of_mem original
  have noConsent := paid.trace.every_original_request_has_no_controller_consents _ request
  refine ⟨paid, crossing, listed, ?_⟩
  rintro (same | signed)
  · exact (distinct_at_boundary _ _ _ crossing) (congrArg community same.symm)
  · rw [show (boundaryRow source word community crossing).1.request.consents = [] from noConsent] at signed
    exact List.not_mem_nil signed

theorem the_victim_loses_exactly_the_displaced_quantity (attack : AggressionAt source word community) :
    attack.item.before.stock attack.victim attack.good -
      (source.native.input.law.step attack.item.before attack.item.request).stock attack.victim attack.good =
      attack.quantity := by
  have balance := source.native.input.law.material_step_balance
    attack.item.before attack.item.request attack.victim attack.good
  change _ =
    flowAt (source.native.input.law.actualDebit attack.item.before attack.item.request) attack.victim attack.good -
      flowAt (source.native.input.law.actualCredit attack.item.before attack.item.request) attack.victim attack.good
  linarith [balance]

theorem in_original_paid_inventory (attack : AggressionAt source word community) :
    { attack.item with index := 0 } ∈
      Quantities.Execution.inventory source (Quantities.Execution.primitiveScript word) := by
  rw [Quantities.Execution.primitive_inventory attack.paid.trace 0]
  have exactOriginal := PublicFunction.execute_physical_of_authorized source.native.input.law source.raw 0 word
    (fun item member => PublicFunction.valid_physical _ _ _ (attack.paid.authorized item member))
    (fun item member => attack.paid.authorized item member)
  change source.native.input.law.execute source.raw 0 word =
    (Physical.Public.interpreter source.native.input).execute source.raw 0 word at exactOriginal
  rw [← exactOriginal]
  exact List.mem_map_of_mem attack.original.1

theorem listed_in_generated_aggressions (attack : AggressionAt source word community) :
    attack ∈ aggressions source word community attack.paid := by
  unfold aggressions
  apply List.mem_filterMap.mpr
  exact ⟨⟨attack.crossing, attack.listed⟩, List.mem_attach _ _,
    by cases attack with
       | mk paid crossing listed unassented => simp only [dif_pos unassented]⟩

end AggressionAt

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
