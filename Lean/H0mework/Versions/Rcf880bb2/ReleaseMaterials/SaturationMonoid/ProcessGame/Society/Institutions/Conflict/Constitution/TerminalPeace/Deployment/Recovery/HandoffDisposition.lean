import H0mework.Versions.Rb5b9c5f8.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Recovery.Quorum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Recovery

variable {Member Point : Type*} [DecidableEq Member]

def forcedFaults (decision incoming noDecision noReady : Finset Member) : Finset Member :=
  (decision ∩ noDecision) ∪ (incoming ∩ noReady)

def Possible (old incoming noDecision noReady : Finset Member) : Prop :=
  ∃ decision : Finset Member, decision ⊆ old ∧ decision.card = 3 ∧
    ((forcedFaults decision incoming noDecision noReady) ∩ old).card ≤ 1 ∧
    ((forcedFaults decision incoming noDecision noReady) ∩ incoming).card ≤ 1

/-- Testing the four outgoing triples is exact for the available role seals.
The converse constructs an allowed fault set and a compatible certificate. -/
theorem possible_iff_completion (old incoming noDecision noReady : Finset Member) :
    Possible old incoming noDecision noReady ↔
      ∃ faults decision : Finset Member, (faults ∩ old).card ≤ 1 ∧ (faults ∩ incoming).card ≤ 1 ∧
        decision ⊆ old ∧ 3 ≤ decision.card ∧ forcedFaults decision incoming noDecision noReady ⊆ faults := by
  constructor
  · rintro ⟨decision, inOld, count, oldBound, newBound⟩
    exact ⟨_, decision, oldBound, newBound, inOld, count.ge, fun _ h => h⟩
  · rintro ⟨faults, decision, oldBound, newBound, inOld, count, h⟩
    obtain ⟨triple, subset, three⟩ := Finset.exists_subset_card_eq count
    have contained : forcedFaults triple incoming noDecision noReady ⊆ faults := by
      intro member hm
      apply h
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨inTriple, sealed⟩ := Finset.mem_inter.mp hm
        exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨subset inTriple, sealed⟩)
      · exact Finset.mem_union_right _ hm
    have narrowed (scope : Finset Member) :
        forcedFaults triple incoming noDecision noReady ∩ scope ⊆ faults ∩ scope := by
      intro member hm
      obtain ⟨forced, included⟩ := Finset.mem_inter.mp hm
      exact Finset.mem_inter.mpr ⟨contained forced, included⟩
    exact ⟨triple, subset.trans inOld, three,
      (Finset.card_le_card (narrowed old)).trans oldBound,
      (Finset.card_le_card (narrowed incoming)).trans newBound⟩

/-- If even the maximum reachable seals permit completion, every subset
still permits it. Issuing those seals cannot authorize a disposition. -/
theorem possible_with_maximal_seals {old incoming noDecision noReady maxDecision maxReady : Finset Member}
    (decisions : noDecision ⊆ maxDecision) (replays : noReady ⊆ maxReady)
    (possible : Possible old incoming maxDecision maxReady) :
    Possible old incoming noDecision noReady := by
  obtain ⟨faults, chosen, oldBound, newBound, included, enough, explained⟩ :=
    (possible_iff_completion old incoming maxDecision maxReady).mp possible
  apply (possible_iff_completion old incoming noDecision noReady).mpr
  refine ⟨faults, chosen, oldBound, newBound, included, enough, ?_⟩
  intro member hm
  apply explained
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨chose, sealed⟩ := Finset.mem_inter.mp hm
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨chose, decisions sealed⟩)
  · obtain ⟨ready, sealed⟩ := Finset.mem_inter.mp hm
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ready, replays sealed⟩)

theorem selected_stays_possible {old incoming noDecision noReady faults decision : Finset Member}
    (oldFaults : (faults ∩ old).card ≤ 1) (newFaults : (faults ∩ incoming).card ≤ 1)
    (outgoing : decision ⊆ old) (chosen : 3 ≤ decision.card)
    (outgoingSeal : ∀ member ∈ decision, member ∈ noDecision → member ∈ faults)
    (incomingSeal : ∀ member ∈ incoming, member ∈ noReady → member ∈ faults) :
    Possible old incoming noDecision noReady := by
  apply (possible_iff_completion old incoming noDecision noReady).mpr
  refine ⟨faults, decision, oldFaults, newFaults, outgoing, chosen, ?_⟩
  intro member hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨v, n⟩ := Finset.mem_inter.mp hm
    exact outgoingSeal member v n
  · obtain ⟨v, n⟩ := Finset.mem_inter.mp hm
    exact incomingSeal member v n

theorem three_outgoing_seals_exclude {old incoming noDecision noReady : Finset Member}
    (four : old.card = 4) (sealedIn : noDecision ⊆ old) (three : 3 ≤ noDecision.card) :
    ¬ Possible old incoming noDecision noReady := by
  rintro ⟨decision, inOld, count, oldBound, _⟩
  obtain ⟨member, chose, sealed, honest⟩ := honest_overlap four oldBound inOld sealedIn count.ge three
  exact honest (Finset.mem_inter.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨chose, sealed⟩), inOld chose⟩)

theorem two_outgoing_seals_can_leave_a_completion :
    Possible ({0, 1, 2, 3} : Finset (Fin 4)) {0, 1, 2, 3} {0, 1} ∅ := by
  refine ⟨{0, 2, 3}, ?_⟩
  decide

/-- When replay never completed, a reachable honest outgoing quorum can
close the attempt even if all nominated verifiers stay absent. -/
theorem interrupted_before_decision_can_be_disposed
    {old incoming noDecision noReady responding : Finset Member} {fullReplay : Prop}
    {decided : Member → Prop} (four : old.card = 4) (sealedIn : noDecision ⊆ old)
    (reachable : 3 ≤ responding.card) (incomplete : ¬ fullReplay)
    (decisionNeedsReplay : ∀ member, decided member → fullReplay)
    (respond : ∀ member ∈ responding, decided member ∨ member ∈ noDecision) :
    ¬ Possible old incoming noDecision noReady := by
  have enough : responding ⊆ noDecision := fun member hm =>
    (respond member hm).resolve_left (fun h => incomplete (decisionNeedsReplay member h))
  exact three_outgoing_seals_exclude four sealedIn (reachable.trans (Finset.card_le_card enough))

variable (roster : Point → Finset Member) (votes ready : Member → Point → Point → Prop)
variable (excluded : Point → Point → Prop)

omit [DecidableEq Member] in
private theorem surviving_certificate
    (sound : ∀ parent next, Certified roster votes ready parent next → ¬ excluded parent next)
    {parent next : Point} (h : Certified roster votes ready parent next) :
    Certified roster (fun member p n => votes member p n ∧ ¬ excluded p n) ready parent next := by
  have live := sound _ _ h
  obtain ⟨⟨voters, included, enough, didVote⟩, replay⟩ := h
  exact ⟨⟨voters, included, enough, fun member hm => ⟨didVote member hm, live⟩⟩, replay⟩

omit [DecidableEq Member] in
private theorem keep_surviving_history
    (sound : ∀ parent next, Certified roster votes ready parent next → ¬ excluded parent next)
    {parent : Point} {history : List Point} (h : History roster votes ready parent history) :
    History roster (fun member p n => votes member p n ∧ ¬ excluded p n) ready parent history := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (surviving_certificate roster votes ready excluded sound h) ih

/-- A verifier may change its vote only after sound exclusion of one of the
alternatives. Every finite history still has one original prefix order. -/
theorem dispositions_preserve_original_prefix_order {faults : Point → Finset Member}
    (four : ∀ parent, (roster parent).card = 4) (oneFault : ∀ parent, (faults parent).card ≤ 1)
    (sound : ∀ parent next, Certified roster votes ready parent next → ¬ excluded parent next)
    (fence : ∀ parent, ∀ member ∉ faults parent, ∀ first second,
      votes member parent first → votes member parent second →
        first = second ∨ excluded parent first ∨ excluded parent second)
    {parent : Point} {left right : List Point}
    (a : History roster votes ready parent left) (b : History roster votes ready parent right) :
    left <+: right ∨ right <+: left := by
  apply original_histories_are_prefix_comparable roster _ ready four oneFault _
    (keep_surviving_history roster votes ready excluded sound a)
    (keep_surviving_history roster votes ready excluded sound b)
  intro p member honest x y vx vy
  exact (fence p member honest x y vx.1 vy.1).resolve_right (fun h => h.elim vx.2 vy.2)

theorem dispositions_preserve_every_cofinal_cut {faults : Point → Finset Member}
    (four : ∀ parent, (roster parent).card = 4) (oneFault : ∀ parent, (faults parent).card ≤ 1)
    (sound : ∀ parent next, Certified roster votes ready parent next → ¬ excluded parent next)
    (fence : ∀ parent, ∀ member ∉ faults parent, ∀ first second,
      votes member parent first → votes member parent second →
        first = second ∨ excluded parent first ∨ excluded parent second)
    {left right : Nat → Point} (sameRoot : left 0 = right 0)
    (a : ∀ n, Certified roster votes ready (left n) (left (n + 1)))
    (b : ∀ n, Certified roster votes ready (right n) (right (n + 1))) :
    ∀ n, left n = right n := by
  apply cofinal_histories_agree roster _ ready four oneFault _ sameRoot
    (fun n => surviving_certificate roster votes ready excluded sound (a n))
    (fun n => surviving_certificate roster votes ready excluded sound (b n))
  intro p member honest x y vx vy
  exact (fence p member honest x y vx.1 vy.1).resolve_right (fun h => h.elim vx.2 vy.2)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Recovery
