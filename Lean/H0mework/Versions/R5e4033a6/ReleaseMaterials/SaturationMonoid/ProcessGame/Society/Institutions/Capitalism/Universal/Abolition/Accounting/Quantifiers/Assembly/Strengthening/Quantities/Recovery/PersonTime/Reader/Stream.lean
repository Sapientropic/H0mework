import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Roster

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Abolition.Root Abolition.Root.Registered
open Intervals

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

structure Stamp (source : C) (script : Script) where
  person : Party
  phase : Phase
  opens : Ordinal source script
  performs : Ordinal source script
  closes : Ordinal source script

instance (source : C) (script : Script) : DecidableEq (Stamp source script) := fun first second =>
  if same : first.person = second.person ∧ first.phase = second.phase ∧
      first.opens.val = second.opens.val ∧ first.performs.val = second.performs.val ∧
      first.closes.val = second.closes.val then
    isTrue (by
      cases first
      cases second
      simp only [Stamp.mk.injEq]
      exact ⟨same.1, same.2.1, Fin.ext same.2.2.1, Fin.ext same.2.2.2.1, Fin.ext same.2.2.2.2⟩)
  else isFalse (fun equal => same (equal ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩))

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} source}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

def Observation.stamp (observation : Observation source meter script) : Stamp source script :=
  ⟨observation.person, observation.phase, observation.opens, observation.performs, observation.closes⟩

theorem Observation.same_span_of_same_stamp
    {first second : Observation source meter script} (same : first.stamp = second.stamp) :
    first.span = second.span := by
  have opens : first.opens = second.opens := congrArg Stamp.opens same
  have closes : first.closes = second.closes := congrArg Stamp.closes same
  unfold Observation.span
  simp only [opens, closes]

/-- The original meter emits a finite stream. Completeness is checked
against its own physical evidence family, before any reader is used. -/
structure SourceStream (source : C) (meter : Meter.{u} source) (script : Script) where
  emitted : List (Observation source meter script)
  exhaustive : ∀ observation : Observation source meter script,
    ∃ original ∈ emitted, original.stamp = observation.stamp

abbrev CoversSource (reported : List (Observation source meter script)) : Prop :=
  ∀ observation : Observation source meter script, ∃ read ∈ reported, read.stamp = observation.stamp

theorem complete_reports_give_exactly_the_original_person_hours
    (reported : List (Observation source meter script)) (covered : CoversSource reported)
    (person : Party) (includes : Phase → Bool) :
    hours reported person includes = hours (roster source meter script) person includes := by
  apply length_eq_of_same_cover
  ext time
  rw [cover_for_iff_original_person_occupation, roster_covers_exactly_the_source_occupations]
  constructor
  · rintro ⟨read, _, owner, phase, occupied⟩
    exact ⟨read, owner, phase, occupied⟩
  · rintro ⟨original, owner, phase, occupied⟩
    obtain ⟨read, listed, same⟩ := covered original
    have samePhase : read.phase = original.phase := congrArg Stamp.phase same
    exact ⟨read, listed, (congrArg Stamp.person same).trans owner,
      samePhase.symm ▸ phase, (Observation.same_span_of_same_stamp same).symm ▸ occupied⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
