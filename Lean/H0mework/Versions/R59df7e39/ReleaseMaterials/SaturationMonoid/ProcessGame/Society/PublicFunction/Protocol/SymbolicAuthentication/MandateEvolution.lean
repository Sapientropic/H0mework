import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cuts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MandateEvolution

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}

def Precedes (first second : Mandate.State Party Technology) : Prop :=
  first = second ∨ first.version < second.version

theorem Precedes.refl (state : Mandate.State Party Technology) : Precedes state state := Or.inl rfl

theorem Precedes.trans {first middle last : Mandate.State Party Technology}
    (front : Precedes first middle) (back : Precedes middle last) : Precedes first last := by
  rcases front with rfl | front
  · exact back
  rcases back with rfl | back
  · exact Or.inr front
  · exact Or.inr (Nat.lt_trans front back)

theorem Precedes.antisymm {first second : Mandate.State Party Technology}
    (front : Precedes first second) (back : Precedes second first) : first = second := by
  rcases front with same | front
  · exact same
  rcases back with same | back
  · exact same.symm
  · exact False.elim (Nat.lt_asymm front back)

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port))

theorem step_preserves_or_advances
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument) :
    Precedes current.technology ((Mandate.law base scope).step current request).technology := by
  by_cases accepted : (Mandate.law base scope).Valid current request
  · rw [RawLaw.step, if_pos accepted]
    cases operation : request.operation with
    | revise actor target =>
      have policy := accepted.1.2
      simp only [Mandate.law, RawLaw.operationAllowed, RawPolicy.eval, operation] at policy
      cases marked : target.last with
      | none => simp [marked] at policy
      | some command =>
        simp only [marked, decide_eq_true_eq] at policy
        have target_exact := policy.2.2.2.2.1
        apply Or.inr
        simpa only [RawLaw.paidStep, operation, target_exact, Mandate.advance_version] using
          Nat.lt_succ_self current.technology.version
    | _ => apply Or.inl; simp only [RawLaw.paidStep, operation]
  · rw [(Mandate.law base scope).rejected_preserves_current _ _ accepted]
    exact Precedes.refl _

theorem execute_span
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (index : Nat) (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    Precedes current.technology ((Mandate.law base scope).execute current index word).final.technology ∧
      ∀ item ∈ ((Mandate.law base scope).execute current index word).items,
        Precedes current.technology item.before.technology ∧
        Precedes item.before.technology ((Mandate.law base scope).execute current index word).final.technology := by
  induction word generalizing current index with
  | nil => exact ⟨Precedes.refl _, by simp [RawLaw.execute]⟩
  | cons request tail ih =>
    have first := step_preserves_or_advances base scope current request
    have rest := ih ((Mandate.law base scope).step current request) (index + 1)
    refine ⟨first.trans rest.1, ?_⟩
    intro item inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨Precedes.refl _, first.trans rest.1⟩
    · have span := rest.2 item inside
      exact ⟨first.trans span.1, span.2⟩

variable {Index : Type} (bound : Mandate.Challenge.ProgrammeFamily base scope Index) (inputs : Index)

abbrev currentAt (ordinal : Nat) := ProgrammeSource.rawCurrent (bound.inputAt inputs)
  (ProgrammeHistory.visitAt (bound.inputAt inputs) ordinal).current
abbrev wordAt (ordinal : Nat) := ProgrammeSource.rawEvent (bound.inputAt inputs)
  (ProgrammeHistory.visitAt (bound.inputAt inputs) ordinal).current

theorem at_successor (ordinal : Nat) :
    currentAt base scope bound inputs (ordinal + 1) =
      (Mandate.law base scope).next (currentAt base scope bound inputs ordinal) (wordAt base scope bound inputs ordinal) := by
  change ProgrammeSource.rawCurrent (bound.inputAt inputs)
    (ProgrammeSource.next (bound.inputAt inputs) (ProgrammeHistory.visitAt (bound.inputAt inputs) ordinal).current) = _
  rw [ProgrammeSource.actual_raw_next, bound.law_exact]

theorem at_step (ordinal : Nat) :
    Precedes (currentAt base scope bound inputs ordinal).technology (currentAt base scope bound inputs (ordinal + 1)).technology := by
  rw [at_successor]
  exact (execute_span base scope _ 0 _).1

theorem at_ordered (first last : Nat) (ordered : first ≤ last) :
    Precedes (currentAt base scope bound inputs first).technology (currentAt base scope bound inputs last).technology := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le ordered
  induction distance with
  | zero => exact Precedes.refl _
  | succ distance ih => exact (ih (by omega)).trans (at_step base scope bound inputs (first + distance))

theorem position_span (position : Mandate.Challenge.Position bound inputs) :
    Precedes (currentAt base scope bound inputs position.ordinal).technology (position.item bound inputs).before.technology ∧
      Precedes (position.item bound inputs).before.technology (currentAt base scope bound inputs (position.ordinal + 1)).technology := by
  have inside := List.get_mem (Registered.traceItems (bound.inputAt inputs)
    (ProgrammeHistory.visitAt (bound.inputAt inputs) position.ordinal).current) position.index
  change (position.item bound inputs) ∈ (bound.inputAt inputs).law.rawItems
    (currentAt base scope bound inputs position.ordinal) (wordAt base scope bound inputs position.ordinal) at inside
  rw [bound.law_exact] at inside
  have span := (execute_span base scope (currentAt base scope bound inputs position.ordinal) 0
    (wordAt base scope bound inputs position.ordinal)).2 _ inside
  rw [at_successor]
  exact span

theorem equal_endpoints_preserve_every_intermediate_snapshot
    (first last : Nat) (same : (currentAt base scope bound inputs first).technology = (currentAt base scope bound inputs last).technology)
    (position : Mandate.Challenge.Position bound inputs)
    (afterFirst : first ≤ position.ordinal) (beforeLast : position.ordinal < last) :
    (position.item bound inputs).before.technology = (currentAt base scope bound inputs first).technology := by
  have span := position_span base scope bound inputs position
  have front := (at_ordered base scope bound inputs first position.ordinal afterFirst).trans span.1
  have back := span.2.trans (at_ordered base scope bound inputs (position.ordinal + 1) last beforeLast)
  rw [← same] at back
  exact (front.antisymm back).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MandateEvolution
