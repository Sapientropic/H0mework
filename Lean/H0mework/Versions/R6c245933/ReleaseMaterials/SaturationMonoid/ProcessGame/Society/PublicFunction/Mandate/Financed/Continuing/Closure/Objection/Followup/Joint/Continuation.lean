import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Lineage

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {start : Inventory fuel}

structure Descendant (original : Row start.cut) (inventory : Inventory fuel) where
  private mk ::
  thread : Thread original.1 inventory.cut
  present : (⟨original.1, thread⟩ : Row inventory.cut) ∈ inventory.frame.rows
  crossing : (Cross.process original.1.2).Run original.2.history.state.current thread.history.state.current

def begin (inventory : Inventory fuel) (row : Row inventory.cut) (inside : row ∈ inventory.frame.rows) :
    Descendant row inventory := ⟨row.2, inside, .nil⟩

def Descendant.step {original : Row start.cut} {inventory : Inventory fuel}
    (descendant : Descendant original inventory) (word : List Action) : Descendant original (submit inventory word) :=
  let transfer := carry inventory word ⟨original.1, descendant.thread⟩ descendant.present
  ⟨transfer.thread, transfer.present, descendant.crossing.concatRuns _ transfer.crossing⟩

def Descendant.complete {original : Row start.cut} {inventory : Inventory fuel}
    (descendant : Descendant original inventory) :
    (Cross.process original.1.2).Run (ResponsibilityState.empty (V fuel original.1.1)) descendant.thread.history.state.current :=
  descendant.thread.history.state.generated

def Descendant.responses {original : Row start.cut} {inventory : Inventory fuel}
    (descendant : Descendant original inventory) : (count : Nat) → Descendant original (run inventory count)
  | 0 => descendant
  | count + 1 => (descendant.responses count).step (emit (run inventory count))

def Descendant.alternating {original : Row start.cut} {inventory : Inventory fuel}
    (descendant : Descendant original inventory) : (words : List (List Action)) → Descendant original (alternate inventory words)
  | [] => descendant
  | word :: tail => ((descendant.step (emit inventory)).step word).alternating tail

def every_original_survives_finite_responses (inventory : Inventory fuel) (row : Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) (count : Nat) : Descendant row (run inventory count) :=
  (begin inventory row inside).responses count

def every_original_survives_finite_alternation (inventory : Inventory fuel) (row : Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) (words : List (List Action)) : Descendant row (alternate inventory words) :=
  (begin inventory row inside).alternating words

def every_newborn_survives_finite_alternation (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) (born : BornAt inventory word index)
    (words : List (List Action)) :
    Descendant (⟨born.row.1, born.thread⟩ : Row (submit inventory word).cut) (alternate (submit inventory word) words) :=
  (begin (submit inventory word) ⟨born.row.1, born.thread⟩ born.present).alternating words

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
