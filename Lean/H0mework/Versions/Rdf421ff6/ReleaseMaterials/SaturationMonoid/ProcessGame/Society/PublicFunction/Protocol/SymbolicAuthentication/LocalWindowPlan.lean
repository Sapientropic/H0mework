import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalService

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowPlan

open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code) (start : Cursor code)

def next (installed : List (Rule code)) (elapsed : Nat) : Rule code :=
  if elapsed < 2 * code.sites then ObservationSupply.protocol vocabulary law start installed
  else LocalService.protocol vocabulary encoding law start installed

-- Future rules are compiled from prior public rules. No actual state, callback,
-- registry, success flag, or private vector of records enters this recursion.
def build : Nat → List (Rule code) → Nat → List (Rule code)
  | 0, _, _ => []
  | rounds + 1, installed, elapsed =>
    let rule := next vocabulary encoding law start installed elapsed
    rule :: build rounds (installed ++ [rule]) (elapsed + 1)

def count (installed : List (Rule code)) := min (4 * code.sites) ((EventStep.seed start).remaining - installed.length)
def supplyCount (installed : List (Rule code)) := min (2 * code.sites) (count start installed)
def serviceCount (installed : List (Rule code)) := count start installed - supplyCount start installed
def produce (installed : List (Rule code)) :=
  let supply := build vocabulary encoding law start (supplyCount start installed) installed 0
  supply ++ List.replicate (serviceCount start installed)
    (LocalService.protocol vocabulary encoding law start (installed ++ supply))

theorem length_build (rounds : Nat) (installed : List (Rule code)) (elapsed : Nat) :
    (build vocabulary encoding law start rounds installed elapsed).length = rounds := by
  induction rounds generalizing installed elapsed with
  | zero => rfl
  | succ rounds ih => simp only [build, List.length_cons, ih]

theorem public_window_has_the_source_clock_bound (installed : List (Rule code)) :
    (produce vocabulary encoding law start installed).length ≤ 4 * code.sites ∧
      (produce vocabulary encoding law start installed).length ≤ (EventStep.seed start).remaining - installed.length := by
  have counted : (produce vocabulary encoding law start installed).length = count start installed := by
    simp only [produce, List.length_append, length_build, List.length_replicate, serviceCount]
    have bounded : supplyCount start installed ≤ count start installed := Nat.min_le_right _ _
    omega
  rw [counted]
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem every_publicly_compiled_rule_is_source_generated (rounds : Nat)
    (installed : List (Rule code)) (elapsed : Nat) (rule : Rule code)
    (_ : rule ∈ build vocabulary encoding law start rounds installed elapsed) : rule ∈ rules code :=
  every_rule_is_source_generated code rule

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowPlan
