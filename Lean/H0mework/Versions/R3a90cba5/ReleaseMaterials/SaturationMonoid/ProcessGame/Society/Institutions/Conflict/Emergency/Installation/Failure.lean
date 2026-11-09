import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Solver
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm (withCutoff)
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (current : RawCurrent Party Good (State Party Technology) Instrument)
  (first second : Party) (unit : Good) (expiry : ℚ)

local notation "Active" => law base (withCutoff scope expiry)
local notation "Review" => request (withCutoff scope expiry)
local notation "Head" => Review current first Command.review
local notation "Middle" => RawLaw.step Active current Head

/-- One refused signature and, when present, its exact unavailable
payer/good cell. This is a view of the native debit, including repeated
entries for the same address. -/
structure Shortage (before : Raw) (instruction : Req) where
  entry : (Party × Good) × ℚ
  original : entry ∈ (Active).debit before instruction
  insufficient : before.stock entry.1.1 entry.1.2 <
    flowAt ((Active).debit before instruction) entry.1.1 entry.1.2

def Shortage.missing {before : Raw} {instruction : Req}
    (short : Shortage base scope expiry before instruction) : ℚ :=
  flowAt ((Active).debit before instruction) short.entry.1.1 short.entry.1.2 -
    before.stock short.entry.1.1 short.entry.1.2

omit [DecidableEq Instrument] in
theorem Shortage.missing_pos {before : Raw} {instruction : Req}
    (short : Shortage base scope expiry before instruction) : 0 < short.missing base scope expiry :=
  sub_pos.mpr short.insufficient

def shortage? (before : Raw) (instruction : Req) : Option (Shortage base scope expiry before instruction) :=
  match inspectList (fun entry : (Party × Good) × ℚ =>
      flowAt ((Active).debit before instruction) entry.1.1 entry.1.2 ≤ before.stock entry.1.1 entry.1.2)
      ((Active).debit before instruction) with
  | .clear _ => none
  | .failure entry original short => some ⟨entry, original, lt_of_not_ge short⟩

inductive ReleaseFailure where
  | vacant (found : current.technology.holder = none)
  | duplicate (found : first = second)
  | firstHeld (found : current.technology.holder = some first)
  | secondHeld (found : current.technology.holder = some second)
  | unpaidFee (found : amount Good scope.revisionCost unit ≤ 0)
  | firstRefused (refused : ¬ (Active).Valid current Head)
      (short : Option (Shortage base scope expiry current Head))
  | secondRefused (refused : ¬ (Active).Valid Middle (Review Middle second Command.review))
      (short : Option (Shortage base scope expiry Middle (Review Middle second Command.review)))

def explainRelease (denied : ¬ ReleaseReady base scope current first second unit expiry) :
    ReleaseFailure base scope current first second unit expiry :=
  if live : current.technology.holder ≠ none then
    if distinct : first ≠ second then
      if independent₁ : current.technology.holder ≠ some first then
        if independent₂ : current.technology.holder ≠ some second then
          if fee : 0 < amount Good scope.revisionCost unit then
            if paid₁ : (Active).Valid current Head then
              .secondRefused (fun paid₂ => denied ⟨live, distinct, independent₁, independent₂, fee, paid₁, paid₂⟩)
                (shortage? base scope expiry Middle (Review Middle second Command.review))
            else .firstRefused paid₁ (shortage? base scope expiry current Head)
          else .unpaidFee (le_of_not_gt fee)
        else .secondHeld (of_not_not independent₂)
      else .firstHeld (of_not_not independent₁)
    else .duplicate (of_not_not distinct)
  else .vacant (of_not_not live)

section CalendarObstruction

variable (initial : RawCurrent Party Good (State Party Technology) Instrument)
  (words : List (RawEvent Party Good Port (State Party Technology) Instrument))

local notation "Slice" => Cell Party Good Port Technology Instrument
local notation "Calendar" => cells base scope (Band.mk (RawCurrent.clock initial) none) initial words

/-- A blocked solver can classify every requested absolute horizon. It
keeps the exact rejected cell and either the unmet original matching
condition or the payer whose actual independent signature failed. -/
inductive CandidateFailure where
  | beforeOrigin (earlier : expiry < initial.clock)
  | afterServiceDue (later : scope.task.deadline < expiry)
  | beforeRelease (cell : Slice) (listed : cell ∈ Calendar) (fits : cell.band.Holds expiry)
      (early : cell.target.clock ≤ expiry)
  | unpaidService (cell : Slice) (listed : cell ∈ Calendar) (fits : cell.band.Holds expiry)
      (missing : ¬ ServiceSafeAt scope.task cell expiry)
  | review (cell : Slice) (listed : cell ∈ Calendar) (service : ServiceSafeAt scope.task cell expiry)
      (failure : ReleaseFailure base scope cell.target first second unit expiry)

def explainCandidate (denied : ¬ Feasible base scope first second unit initial words expiry) :
    CandidateFailure base scope first second unit expiry initial words :=
  if before : expiry < initial.clock then .beforeOrigin before
  else if later : scope.task.deadline < expiry then .afterServiceDue later
  else
    match inspectList (fun cell : Slice => ¬ cell.band.Holds expiry) Calendar with
    | .clear impossible => False.elim (by
        obtain ⟨cell, listed, fit⟩ := cells_cover_all_deadlines base scope ⟨initial.clock, none⟩ initial words expiry
          ⟨fun _ same => (Option.some.inj same) ▸ le_of_not_gt before,
            fun _ same => by cases same⟩
        exact impossible cell listed fit)
    | .failure cell listed notAbsent =>
      let fit := of_not_not notAbsent
      if early : cell.target.clock ≤ expiry then .beforeRelease cell listed fit early
      else
        match inspectList (fun assigned => ¬ (termBand scope.task cell assigned).Holds expiry)
            (safeAssignments scope.task cell) with
        | .clear unpaid => .unpaidService cell listed fit (fun service => by
            obtain ⟨_, assigned, present, matched⟩ :=
              (safe_service_iff_listed_assignment scope.task cell expiry).mp service
            exact unpaid assigned present matched)
        | .failure assigned present found =>
          let service := (safe_service_iff_listed_assignment scope.task cell expiry).mpr
            ⟨le_of_not_gt later, assigned, present, of_not_not found⟩
          .review cell listed service
            (explainRelease base scope cell.target first second unit expiry
              (fun review => denied ⟨cell, listed, service, review⟩))

end CalendarObstruction

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
