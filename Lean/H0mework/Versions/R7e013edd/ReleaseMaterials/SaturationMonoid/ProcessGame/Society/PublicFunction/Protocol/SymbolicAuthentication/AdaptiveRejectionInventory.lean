import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveReceptionBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionInventory
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryDeadline AdaptiveReceptionBudget

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

def identities (past : List (EventHistory.Stage (code := code))) : Finset (Fin code.sites × Nat) :=
  Finset.univ.biUnion fun receiver =>
    ((ReceptionEvidence.observed start past vocabulary encoding law receiver).map (fun entry => (receiver, entry.index))).toFinset

theorem mem_identities (past : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (index : Nat) :
    (receiver, index) ∈ identities start vocabulary encoding law past ↔
      ∃ entry ∈ ReceptionEvidence.observed start past vocabulary encoding law receiver, entry.index = index := by
  simp only [identities, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨other, entry, inside, same, coordinate⟩
    subst other
    exact ⟨entry, inside, coordinate⟩
  · rintro ⟨entry, inside, coordinate⟩
    exact ⟨receiver, entry, inside, rfl, coordinate⟩

theorem one_actual_delivery_has_at_most_one_intended_rejection_identity
    (past : List (EventHistory.Stage (code := code))) (first second : Fin code.sites × Nat)
    (one : first ∈ identities start vocabulary encoding law past)
    (two : second ∈ identities start vocabulary encoding law past) (same : first.2 = second.2) : first = second := by
  obtain ⟨a, _, ai⟩ := (mem_identities start vocabulary encoding law past first.1 first.2).mp one
  obtain ⟨b, _, bi⟩ := (mem_identities start vocabulary encoding law past second.1 second.2).mp two
  have index : a.index = b.index := ai.trans (same.trans bi.symm)
  have wire : a.wire = b.wire := by
    have incoming := a.incoming
    rw [index, b.incoming] at incoming
    exact Option.some.inj incoming.symm
  apply Prod.ext
  · exact a.intended.symm.trans ((congrArg (fun w => w.recipient) wire).trans b.intended)
  · exact same

variable (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

theorem records_are_the_actual_indexed_rows (n : Nat) :
    StageTrace.records start (stages protocols rivals n) = (List.range n).map (row start protocols rivals) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [records_succ, ih, List.range_succ, List.map_append]; rfl

theorem delivery_indices_have_the_actual_delivery_count (n : Nat) :
    (((List.range n).filter fun i => delivery (row start protocols rivals i)).toFinset).card ≤
      tally start protocols rivals delivery n := by
  unfold tally
  rw [records_are_the_actual_indexed_rows, List.filter_map, List.length_map]
  exact List.toFinset_card_le _

theorem actual_rejection_identities_fit_the_source_reception_budget
    (allowance stop : Nat) (compliant : Compliant start protocols rivals allowance stop) :
    ∀ n ≤ stop, (identities start vocabulary encoding law (stages protocols rivals n)).card ≤ capacity (code := code) := by
  intro n bounded
  let inventory := identities start vocabulary encoding law (stages protocols rivals n)
  have unique : Set.InjOn Prod.snd (↑inventory : Set (Fin code.sites × Nat)) := by
    intro first one second two same
    exact one_actual_delivery_has_at_most_one_intended_rejection_identity start vocabulary encoding law _ first second one two same
  have contained : inventory.image Prod.snd ⊆ ((List.range n).filter fun i => delivery (row start protocols rivals i)).toFinset := by
    intro index included
    obtain ⟨id, inside, rfl⟩ := Finset.mem_image.mp included
    obtain ⟨entry, _, coordinate⟩ := (mem_identities start vocabulary encoding law _ id.1 id.2).mp inside
    have before := ReceptionEvidence.bounded start _ vocabulary encoding law id.1 entry
    rw [stage_count] at before
    have actual := entry.actual
    rw [row_at start protocols rivals n entry.index before] at actual
    have same : row start protocols rivals entry.index = entry.row := Option.some.inj actual
    have delivered := ReceptionEvidence.incoming_is_an_actual_delivery start _ vocabulary encoding law id.1 entry
    have isDelivery : delivery entry.row = true := by
      unfold delivery
      unfold StageReception.delivered at delivered
      split at delivered <;> try contradiction
      split at delivered <;> try contradiction
      simp_all
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    rw [← coordinate]
    exact ⟨List.mem_range.mpr before, same ▸ isDelivery⟩
  have count := Finset.card_le_card contained
  rw [Finset.card_image_of_injOn unique] at count
  exact count.trans ((delivery_indices_have_the_actual_delivery_count start protocols rivals n).trans
    (every_compliant_adaptive_prefix_has_a_source_generated_reception_budget start protocols rivals allowance stop compliant n bounded))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionInventory
