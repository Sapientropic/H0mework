import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Path

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (script : List (Option (Compile.RawInput Party Good Port Technology Instrument)))

abbrev finalCut := cutAt (Birth.attacked claim) script script.length
abbrev finalFrame := (finalCut claim script).native.frame

/-- The supplied actual prefix is indexed by original script positions.
After it, the original final frame provides its own structural successors. -/
abbrev Cursor := Fin script.length ⊕ (finalFrame claim script).V.Current

def nextCursor : Cursor claim script → Cursor claim script
  | .inl position =>
    if later : position.val + 1 < script.length then .inl ⟨position.val + 1, later⟩
    else .inr (finalCut claim script).native.visit.current
  | .inr original => .inr ((finalFrame claim script).successor original).targetCurrent

def positionAt (position : Nat) : Cursor claim script :=
  if inside : position < script.length then .inl ⟨position, inside⟩
  else .inr (finalCut claim script).native.visit.current

theorem positionAt_step (position : Nat) (inside : position < script.length) :
    nextCursor claim script (positionAt claim script position) = positionAt claim script (position + 1) := by
  simp only [positionAt, dif_pos inside, nextCursor]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
