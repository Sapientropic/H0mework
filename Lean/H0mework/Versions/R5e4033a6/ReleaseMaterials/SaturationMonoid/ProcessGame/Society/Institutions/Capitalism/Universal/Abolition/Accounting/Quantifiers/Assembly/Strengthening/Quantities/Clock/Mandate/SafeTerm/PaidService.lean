import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Native
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Assignments

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm

open Source.Program PublicFunction PublicFunction.Mandate
open OutstandingSource.History.NativeService
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity
open Due.Service.Mixed

private def listed {size : Nat} (carrier : Finset (Fin size)) : List (Fin size) :=
  (List.finRange size).filter fun member => decide (member ∈ carrier)

private theorem listed_exact {size : Nat} (carrier : Finset (Fin size)) :
    (listed carrier).toFinset = carrier := by
  ext member
  simp [listed]

private def candidates {m n : Nat} (geometry : CanonicalBipartiteFeasibility (Fin m) (Fin n)) :=
  assignments (eligibility geometry) (listed geometry.leftCarrier) (listed geometry.rightCarrier)

private theorem listed_match_iff {m n : Nat}
    (geometry : CanonicalBipartiteFeasibility (Fin m) (Fin n)) (matching : Finset (Fin m × Fin n)) :
    matching ∈ candidates geometry ↔ matching ∈ geometry.matchings ∧ matching.card = geometry.leftCarrier.card := by
  have distinct : (listed geometry.leftCarrier).Nodup := (List.nodup_finRange m).filter _
  exact (assignments_are_exact _ _ _ distinct matching).trans
    (original_and_full_iff_assignment geometry _ _ (listed_exact _) (listed_exact _) matching).symm

def completeMatching {m n : Nat} (geometry : CanonicalBipartiteFeasibility (Fin m) (Fin n)) :
    Option {matching : Finset (Fin m × Fin n) //
      matching ∈ geometry.matchings ∧ matching.card = geometry.leftCarrier.card} :=
  ((candidates geometry).attach.head?).map fun found => ⟨found.val, (listed_match_iff geometry _).mp found.property⟩

theorem complete_matching_iff {m n : Nat}
    (geometry : CanonicalBipartiteFeasibility (Fin m) (Fin n)) :
    (completeMatching geometry).isSome = true ↔ geometry.maximumMatchingCapacity = geometry.leftCarrier.card := by
  rw [full_capacity_iff_there_is_a_complete_matching]
  constructor
  · intro found
    let matched := (completeMatching geometry).get found
    exact ⟨matched.val, matched.property⟩
  · rintro ⟨matching, original, full⟩
    have possible := (listed_match_iff geometry matching).mpr ⟨original, full⟩
    simp only [completeMatching, Option.isSome_map, List.isSome_head?]
    cases available : candidates geometry with
    | nil => rw [available] at possible; exact (List.not_mem_nil possible).elim
    | cons head tail =>
      intro empty
      have lengths := congrArg List.length empty
      simp at lengths

section Native

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

/-- Reuse the existing native service decision, with the exact finite
assignment search for distinct originally paid uses. -/
def scanPaidService (bound : BoundSource base scope) (past suffix : Inputs) :
    Term.Decision bound past suffix :=
  let combined := past ++ suffix
  let archive := (frameAt bound.source combined (combined.length + 2)).payments
  match Material.inspectList (fun slot : bound.source.Slot => (archive slot).isSome = true)
      (List.finRange bound.source.seed.task.slots.length) with
  | .failure slot _ failed =>
    .blocked (.service slot (((Term.serviceThread bound past suffix slot).native_live_iff_unpaid bound.source).mpr
      (by cases actual : archive slot with
          | none => exact actual
          | some _ => exact (failed (by rw [actual]; rfl)).elim)))
  | .clear paid =>
    let geometry := Term.serviceGeometry bound past suffix
    match scanned : completeMatching geometry with
    | none => .blocked (.overlap (lt_of_le_of_ne geometry.maximumMatchingCapacity_le_left
        (fun equal => by
          have complete := (complete_matching_iff geometry).mpr equal
          rw [scanned] at complete
          cases complete)))
    | some _ =>
      if inactive : (Term.target bound past suffix).technology.holder = none ∧
          (Term.target bound past suffix).technology.offered = none then
        .paid {
          slots := fun slot => ((Term.serviceThread bound past suffix slot).native_terminal_iff_recorded bound.source).mpr
            (by cases actual : archive slot with
                | none => have found := paid slot (List.mem_finRange slot); rw [actual] at found; cases found
                | some ordinal => exact ⟨ordinal, actual⟩)
          distinctDebits := (complete_matching_iff geometry).mp (by rw [scanned]; rfl)
          closed := inactive
          next := OutstandingSource.History.actual_next bound.source combined _ }
      else .blocked (.authority inactive)

end Native

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
