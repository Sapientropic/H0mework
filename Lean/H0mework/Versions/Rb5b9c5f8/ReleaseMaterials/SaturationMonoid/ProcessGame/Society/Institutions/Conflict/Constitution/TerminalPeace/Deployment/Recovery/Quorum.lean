import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Recovery

variable {Member Point : Type*} [DecidableEq Member]

/-- A durable write and a fresh read in the same four-member epoch share a
verifier outside the fault set. -/
theorem honest_overlap {members writes reads faults : Finset Member}
    (four : members.card = 4) (oneFault : faults.card ≤ 1)
    (writesIn : writes ⊆ members) (readsIn : reads ⊆ members)
    (writeQuorum : 3 ≤ writes.card) (readQuorum : 3 ≤ reads.card) :
    ∃ member, member ∈ writes ∧ member ∈ reads ∧ member ∉ faults := by
  have unionBound := Finset.card_le_card (Finset.union_subset writesIn readsIn)
  have sum := Finset.card_union_add_card_inter writes reads
  by_contra! none
  have contained : writes ∩ reads ⊆ faults := by
    intro member inside
    obtain ⟨write, read⟩ := Finset.mem_inter.mp inside
    exact none member write read
  have bound := Finset.card_le_card contained
  omega

theorem two_reads_can_miss_an_honest_durable_verifier :
    ∃ writes reads faults : Finset (Fin 4), writes.card = 3 ∧ reads.card = 2 ∧ faults.card = 1 ∧
      ∀ member ∈ writes, member ∈ reads → member ∈ faults := by
  refine ⟨{0, 1, 2}, {2, 3}, {2}, ?_⟩
  decide

variable (roster : Point → Finset Member) (votes ready : Member → Point → Point → Prop)

/-- Every actual handoff consumes the outgoing quorum at its original parent.
The entire incoming roster must replay that same proposed successor. -/
def Certified (parent next : Point) : Prop :=
  (∃ signers : Finset Member,
    signers ⊆ roster parent ∧ 3 ≤ signers.card ∧ ∀ member ∈ signers, votes member parent next) ∧
  (roster next ≠ roster parent → ∀ member ∈ roster next, ready member parent next)

theorem unique_successor {faults : Point → Finset Member}
    (four : ∀ parent, (roster parent).card = 4) (oneFault : ∀ parent, (faults parent).card ≤ 1)
    (fence : ∀ parent, ∀ member ∉ faults parent, ∀ first second,
      votes member parent first → votes member parent second → first = second)
    {parent first second : Point}
    (a : Certified roster votes ready parent first) (b : Certified roster votes ready parent second) :
    first = second := by
  obtain ⟨writes, writesIn, writeQuorum, votedFirst⟩ := a.1
  obtain ⟨reads, readsIn, readQuorum, votedSecond⟩ := b.1
  obtain ⟨member, write, read, honest⟩ :=
    honest_overlap (four parent) (oneFault parent) writesIn readsIn writeQuorum readQuorum
  exact fence parent member honest first second (votedFirst member write) (votedSecond member read)

inductive History : Point → List Point → Prop
  | nil (parent : Point) : History parent []
  | cons {parent next : Point} {rest : List Point} :
      Certified roster votes ready parent next → History next rest → History parent (next :: rest)

/-- There is one recoverable prefix order for arbitrarily many certified
changes of roster. Successive rosters may be disjoint. -/
theorem original_histories_are_prefix_comparable {faults : Point → Finset Member}
    (four : ∀ parent, (roster parent).card = 4) (oneFault : ∀ parent, (faults parent).card ≤ 1)
    (fence : ∀ parent, ∀ member ∉ faults parent, ∀ first second,
      votes member parent first → votes member parent second → first = second)
    {parent : Point} {left right : List Point}
    (a : History roster votes ready parent left) (b : History roster votes ready parent right) :
    left <+: right ∨ right <+: left := by
  induction a generalizing right with
  | nil => exact Or.inl List.nil_prefix
  | cons first _ ih =>
      cases b with
      | nil => exact Or.inr List.nil_prefix
      | cons second tail =>
          cases unique_successor roster votes ready four oneFault fence first second
          rcases ih tail with shorter | longer
          · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, shorter⟩)
          · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, longer⟩)

/-- Arbitrarily many later epochs still determine the same original point at
every common write index. -/
theorem cofinal_histories_agree {faults : Point → Finset Member}
    (four : ∀ parent, (roster parent).card = 4) (oneFault : ∀ parent, (faults parent).card ≤ 1)
    (fence : ∀ parent, ∀ member ∉ faults parent, ∀ first second,
      votes member parent first → votes member parent second → first = second)
    {left right : Nat → Point} (sameRoot : left 0 = right 0)
    (a : ∀ n, Certified roster votes ready (left n) (left (n + 1)))
    (b : ∀ n, Certified roster votes ready (right n) (right (n + 1))) :
    ∀ n, left n = right n := by
  intro n
  induction n with
  | zero => exact sameRoot
  | succ n ih =>
      exact unique_successor roster votes ready four oneFault fence (a n) (ih.symm ▸ b n)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Recovery
