import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceClockTermination

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorEnvelope
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

namespace Pool
variable {Key Actor : Type} [DecidableEq Key] [DecidableEq Actor]

def actors (owner : Key → Actor) (initial : Finset Key) : Finset Actor := initial.image owner

def affected (owner : Key → Actor) (initial : Finset Key) (cuts : List (Finset Key)) : Finset Actor :=
  (initial.filter fun key => cuts.any fun offered => decide (key ∉ offered)).image owner

def retained (owner : Key → Actor) (initial : Finset Key) (cuts : List (Finset Key)) : Finset Key :=
  initial.filter fun key => owner key ∉ affected owner initial cuts

theorem affected_iff (owner : Key → Actor) (initial : Finset Key) (cuts : List (Finset Key)) (actor : Actor) :
    actor ∈ affected owner initial cuts ↔
      ∃ key ∈ initial, owner key = actor ∧ ∃ offered ∈ cuts, key ∉ offered := by
  simp only [affected,Finset.mem_image,Finset.mem_filter,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨key,⟨member,cut⟩,same⟩
    exact ⟨key,member,same,cut⟩
  · rintro ⟨key,member,same,cut⟩
    exact ⟨key,⟨member,cut⟩,same⟩

theorem retained_key_is_the_same_offered_slot_at_every_cut
    (owner : Key → Actor) (initial : Finset Key) (cuts : List (Finset Key)) (key : Key)
    (member : key ∈ retained owner initial cuts) : key ∈ initial ∧ ∀ offered ∈ cuts, key ∈ offered := by
  obtain ⟨initialMember,unaffected⟩ := Finset.mem_filter.mp member
  refine ⟨initialMember,?_⟩
  intro offered inside
  by_contra absent
  exact unaffected ((affected_iff owner initial cuts (owner key)).mpr ⟨key,initialMember,rfl,offered,inside,absent⟩)

theorem identity_surplus_generates_a_fixed_original_slot
    (owner : Key → Actor) (initial : Finset Key) (cuts : List (Finset Key))
    (surplus : (affected owner initial cuts).card < (actors owner initial).card) :
    (retained owner initial cuts).Nonempty := by
  have survivor : ∃ actor ∈ actors owner initial, actor ∉ affected owner initial cuts := by
    by_contra! absent
    have bound := Finset.card_le_card (show actors owner initial ⊆ affected owner initial cuts from absent)
    omega
  obtain ⟨actor,member,unaffected⟩ := survivor
  obtain ⟨key,initialMember,same⟩ := Finset.mem_image.mp member
  exact ⟨key,Finset.mem_filter.mpr ⟨initialMember,by simpa only [same] using unaffected⟩⟩

theorem actual_extension_keeps_every_affected_identity
    (owner : Key → Actor) (initial : Finset Key) (past more : List (Finset Key)) :
    affected owner initial past ⊆ affected owner initial (past ++ more) := by
  intro actor member
  obtain ⟨key,inside,same,offered,present,absent⟩ := (affected_iff owner initial past actor).mp member
  exact (affected_iff owner initial (past ++ more) actor).mpr
    ⟨key,inside,same,offered,List.mem_append_left _ present,absent⟩
end Pool

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law

def offered (past : JointResponse.Stages model) : Finset (Fin model.source.code.sites) :=
  Finset.univ.filter fun worker => (NativeServiceStanding.offer model start past worker).isSome

def initial (past : JointResponse.Stages model) (first : Nat) :=
  offered model start (atCut model start vocabulary encoding law past first)

-- Completed cuts impose no future standing obligation. Every retained view is
-- recomputed from the original runner at its own actual pre-dispatch prefix.
def views (past : JointResponse.Stages model) (first width : Nat) : List (Finset (Fin model.source.code.sites)) :=
  (List.range width).filterMap fun offset =>
    if JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (first + offset))
    then none else some (offered model start (atCut model start vocabulary encoding law past (first + offset)))

abbrev candidates (past : JointResponse.Stages model) (first : Nat) :=
  Pool.actors model.source.code.siteParty (initial model start vocabulary encoding law past first)
abbrev affected (past : JointResponse.Stages model) (first width : Nat) :=
  Pool.affected model.source.code.siteParty (initial model start vocabulary encoding law past first)
    (views model start vocabulary encoding law past first width)
abbrev retained (past : JointResponse.Stages model) (first width : Nat) :=
  Pool.retained model.source.code.siteParty (initial model start vocabulary encoding law past first)
    (views model start vocabulary encoding law past first width)

structure Survivor (past : JointResponse.Stages model) (first width : Nat) where
  private mk ::
  worker : Fin model.source.code.sites
  member : worker ∈ retained model start vocabulary encoding law past first width

inductive Selection (past : JointResponse.Stages model) (first width : Nat) where
  | retained (survivor : Survivor model start vocabulary encoding law past first width)
  | noInitialOffer
  | identityBudgetExhausted

def produce (past : JointResponse.Stages model) (first width : Nat) : Selection model start vocabulary encoding law past first width :=
  match found : (List.finRange model.source.code.sites).find?
      (fun worker => decide (worker ∈ retained model start vocabulary encoding law past first width)) with
  | some worker => .retained ⟨worker,of_decide_eq_true (List.find?_some
      (p := fun worker => decide (worker ∈ retained model start vocabulary encoding law past first width)) found)⟩
  | none => if candidates model start vocabulary encoding law past first = ∅ then .noInitialOffer else .identityBudgetExhausted

theorem source_identity_surplus_forces_the_retained_branch
    (past : JointResponse.Stages model) (first width : Nat)
    (surplus : (affected model start vocabulary encoding law past first width).card <
      (candidates model start vocabulary encoding law past first).card) :
    ∃ survivor, produce model start vocabulary encoding law past first width = .retained survivor := by
  obtain ⟨worker,member⟩ := Pool.identity_surplus_generates_a_fixed_original_slot
    model.source.code.siteParty _ _ surplus
  unfold produce
  split
  · exact ⟨_,rfl⟩
  · rename_i absent
    have missing := List.find?_eq_none.mp absent worker (List.mem_finRange _)
    exact False.elim (missing (decide_eq_true member))

theorem the_budget_exhausted_branch_has_no_surviving_original_slot
    (past : JointResponse.Stages model) (first width : Nat)
    (rejected : produce model start vocabulary encoding law past first width = .identityBudgetExhausted) :
    retained model start vocabulary encoding law past first width = ∅ ∧
    candidates model start vocabulary encoding law past first ≠ ∅ := by
  unfold produce at rejected
  split at rejected
  · contradiction
  · rename_i absent
    split at rejected
    · contradiction
    · rename_i nonempty
      refine ⟨?_,nonempty⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro worker member
      exact List.find?_eq_none.mp absent worker (List.mem_finRange _) (decide_eq_true member)

theorem the_generated_survivor_has_an_actual_offer_at_every_unfinished_cut
    (past : JointResponse.Stages model) (first width : Nat)
    (survivor : Survivor model start vocabulary encoding law past first width)
    (offset : Nat) (inside : offset < width)
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past (first + offset))) :
    (NativeServiceStanding.offer model start
      (atCut model start vocabulary encoding law past (first + offset)) survivor.worker).isSome = true := by
  have actual := Pool.retained_key_is_the_same_offered_slot_at_every_cut
    model.source.code.siteParty _ _ survivor.worker survivor.member
  have present : offered model start (atCut model start vocabulary encoding law past (first + offset)) ∈
      views model start vocabulary encoding law past first width := by
    apply List.mem_filterMap.mpr
    exact ⟨offset,List.mem_range.mpr inside,by simp only [if_neg unfinished]⟩
  exact (Finset.mem_filter.mp (actual.2 _ present)).2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorEnvelope
