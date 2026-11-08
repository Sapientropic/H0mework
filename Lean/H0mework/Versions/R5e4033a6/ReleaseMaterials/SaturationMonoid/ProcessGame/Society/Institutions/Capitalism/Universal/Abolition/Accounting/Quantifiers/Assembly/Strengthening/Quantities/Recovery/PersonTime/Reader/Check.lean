import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Reader.Stream

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Abolition.Root Abolition.Root.Registered

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} source}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "O" => Observation source meter script
local notation "Key" => Stamp source script

private inductive Scan (expected : List O) (received : List Key)
  | complete (seen : ∀ original ∈ expected, original.stamp ∈ received)
  | missing (original : O) (emitted : original ∈ expected) (absent : original.stamp ∉ received)

private def scan : (expected : List O) → (received : List Key) → Scan expected received
  | [], _ => .complete fun _ listed => (List.not_mem_nil listed).elim
  | original :: later, received =>
    if present : original.stamp ∈ received then
      match scan later received with
      | .complete seen => .complete fun observation listed =>
        (List.mem_cons.mp listed).elim (fun same => same.symm ▸ present) (seen observation)
      | .missing unread listed absent => .missing unread (List.mem_cons_of_mem _ listed) absent
    else .missing original List.mem_cons_self present

structure Missing (stream : SourceStream source meter script) (reported : List O) where
  observation : O
  emitted : observation ∈ stream.emitted
  unread : observation.stamp ∉ reported.map Observation.stamp

inductive ReadResult (stream : SourceStream source meter script) (reported : List O)
  | complete (covered : CoversSource reported)
  | missing (issue : Missing stream reported)

/-- Reads are checked by their exact original keys. The first missing
record remains a typed original observation with its actor and ordinals. -/
def read (stream : SourceStream source meter script) (reported : List O) :
    ReadResult stream reported :=
  match scan stream.emitted (reported.map Observation.stamp) with
  | .missing original emitted unread => .missing ⟨original, emitted, unread⟩
  | .complete seen => .complete fun observation => by
    obtain ⟨original, listed, same⟩ := stream.exhaustive observation
    obtain ⟨report, read, stamp⟩ := List.mem_map.mp (seen original listed)
    exact ⟨report, read, stamp.trans same⟩

def ReadResult.missingStamp {stream : SourceStream source meter script} {reported : List O} :
    ReadResult stream reported → Option Key
  | .complete _ => none
  | .missing issue => some issue.observation.stamp

theorem a_missing_record_refutes_complete_reading {stream : SourceStream source meter script}
    {reported : List O} (issue : Missing stream reported) : ¬ CoversSource reported := by
  intro covered
  obtain ⟨report, listed, same⟩ := covered issue.observation
  exact issue.unread (List.mem_map.mpr ⟨report, listed, same⟩)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
