import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Demand

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Inspection where
  | pending (origin : Financial.InstructionOrigin window.input) (original : origin ∈ window.pending)
      (readout : Financial.Installation.Cursor.PendingAt window.input origin)
  | clear (accounted : window.Accounted) (empty : demands window = [])
  | assessed (claim : Claim window) (original : assess window = some claim)

def inspect : Inspection window :=
  match pending : window.pending with
  | origin :: rest => .pending origin (by rw [pending]; exact List.mem_cons_self)
      (Financial.Installation.Cursor.pendingAt window.input origin)
  | [] =>
      match source : assess window with
      | some claim => .assessed claim source
      | none => .clear pending (by
          by_contra nonempty
          have complete : window.Accounted := pending
          rw [assess,dif_pos complete,dif_pos nonempty] at source
          cases source)

theorem an_unprocessed_original_row_cannot_issue_a_new_claim
    (pending : window.pending ≠ []) : assess window = none := by
  unfold assess
  exact dif_neg pending

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
