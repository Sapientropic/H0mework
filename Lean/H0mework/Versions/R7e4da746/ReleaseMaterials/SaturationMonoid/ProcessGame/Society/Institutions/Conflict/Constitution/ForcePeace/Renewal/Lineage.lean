import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Command

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "M" => State Party Technology

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))

private def after (item : Item) := ((law base scope).step item.before item.request).technology

def Keeps (slot : M → Option Party) (candidate : Party) (item : Item) : Prop :=
  slot item.before.technology = some candidate ∧ slot (after base scope item) = some candidate

/-- The actual proposal still governs the offer at the accepting item. -/
def LiveOffer (items : List Item) (candidate : Party) : Prop :=
  ∃ lead proposal tail, items = lead ++ proposal :: tail ∧
    PaidCommand base scope proposal (.propose candidate) ∧
    ∀ item ∈ tail, Keeps base scope State.offered candidate item

/-- The two original signatures are ordered by inventory position even on the
same clock. Only intervening steps preserving the offer and later steps
preserving the holder can support this grant. -/
def LiveGrant (items : List Item) (candidate : Party) : Prop :=
  ∃ lead proposal between acceptance tail, items = lead ++ proposal :: (between ++ acceptance :: tail) ∧
    PaidCommand base scope proposal (.propose candidate) ∧
    PaidCommand base scope acceptance .accept ∧ acceptance.request.signer = candidate ∧
    (∀ item ∈ between, Keeps base scope State.offered candidate item) ∧
    (∀ item ∈ tail, Keeps base scope State.holder candidate item)

variable {base scope}

private theorem LiveOffer.snoc {items : List Item} {candidate : Party}
    (offer : LiveOffer base scope items candidate) (item : Item) (kept : Keeps base scope State.offered candidate item) :
    LiveOffer base scope (items ++ [item]) candidate := by
  obtain ⟨lead, proposal, tail, position, paid, later⟩ := offer
  refine ⟨lead, proposal, tail ++ [item], ?_, paid, ?_⟩
  · rw [position]
    simp only [List.append_assoc, List.cons_append]
  · intro old listed
    rcases List.mem_append.mp listed with earlier | last
    · exact later old earlier
    · rwa [List.mem_singleton.mp last]

private theorem LiveOffer.accept {items : List Item} {candidate : Party}
    (offer : LiveOffer base scope items candidate) {item : Item} (paid : PaidCommand base scope item .accept)
    (signer : item.request.signer = candidate) : LiveGrant base scope (items ++ [item]) candidate := by
  obtain ⟨lead, proposal, between, position, proposed, stillOffered⟩ := offer
  refine ⟨lead, proposal, between, item, [], ?_, proposed, paid, signer, stillOffered, ?_⟩
  · rw [position]
    simp only [List.append_assoc, List.cons_append]
  · simp

private theorem LiveGrant.snoc {items : List Item} {candidate : Party}
    (grant : LiveGrant base scope items candidate) (item : Item) (kept : Keeps base scope State.holder candidate item) :
    LiveGrant base scope (items ++ [item]) candidate := by
  obtain ⟨lead, proposal, between, acceptance, tail, position, proposed, accepted, signer, offered, holder⟩ := grant
  refine ⟨lead, proposal, between, acceptance, tail ++ [item], ?_, proposed, accepted, signer, offered, ?_⟩
  · rw [position]
    simp only [List.append_assoc, List.cons_append]
  · intro old listed
    rcases List.mem_append.mp listed with earlier | last
    · exact holder old earlier
    · rwa [List.mem_singleton.mp last]

variable (base scope)

private structure Origin (items : List Item) (current : M) : Prop where
  offer : ∀ candidate, current.offered = some candidate → LiveOffer base scope items candidate
  grant : ∀ candidate, current.holder = some candidate → LiveGrant base scope items candidate

private theorem Origin.advance {items : List Item} {item : Item}
    (origin : Origin base scope items item.before.technology)
    (licensed : (law base scope).Valid item.before item.request) :
    Origin base scope (items ++ [item]) (after base scope item) := by
  have keepOffer (unchanged : (after base scope item).offered = item.before.technology.offered)
      (candidate : Party) (offered : (after base scope item).offered = some candidate) :
      LiveOffer base scope (items ++ [item]) candidate :=
    (origin.offer candidate (unchanged.symm.trans offered)).snoc item ⟨unchanged.symm.trans offered, offered⟩
  have keepHolder (unchanged : (after base scope item).holder = item.before.technology.holder)
      (candidate : Party) (holder : (after base scope item).holder = some candidate) :
      LiveGrant base scope (items ++ [item]) candidate :=
    (origin.grant candidate (unchanged.symm.trans holder)).snoc item ⟨unchanged.symm.trans holder, holder⟩
  rcases classify_material_item base scope item licensed with unchanged | ⟨command, paid⟩
  · exact ⟨keepOffer (congrArg State.offered unchanged), keepHolder (congrArg State.holder unchanged)⟩
  · have updated : after base scope item = PublicFunction.Mandate.advance scope item.before command := paid.after
    cases command with
    | propose next =>
      refine ⟨?_, keepHolder (by rw [updated]; rfl)⟩
      intro candidate offered
      have same : next = candidate := by
        simpa only [updated, PublicFunction.Mandate.advance, Option.some.injEq] using offered
      subst candidate
      exact ⟨items, item, [], rfl, paid, by simp⟩
    | accept =>
      refine ⟨by simp [updated, PublicFunction.Mandate.advance], ?_⟩
      intro candidate holder
      have offered : item.before.technology.offered = some candidate := by
        simpa only [updated, PublicFunction.Mandate.advance] using holder
      exact (origin.offer candidate offered).accept paid (Option.some.inj (paid.canRun.1.symm.trans offered))
    | renew =>
      exact ⟨by simp [updated, PublicFunction.Mandate.advance], keepHolder (by rw [updated]; rfl)⟩
    | exit => exact ⟨by simp [updated, PublicFunction.Mandate.advance], by simp [updated, PublicFunction.Mandate.advance]⟩
    | revoke => exact ⟨by simp [updated, PublicFunction.Mandate.advance], by simp [updated, PublicFunction.Mandate.advance]⟩
    | review =>
      by_cases expired : scope.task.deadline < item.before.clock
      · exact ⟨by simp [updated, PublicFunction.Mandate.advance, expired],
          by simp [updated, PublicFunction.Mandate.advance, expired]⟩
      · exact ⟨keepOffer (by simp [updated, PublicFunction.Mandate.advance, expired]),
          keepHolder (by simp [updated, PublicFunction.Mandate.advance, expired])⟩

private theorem MaterialTrace.origin {start final : M} {items prior : List Item}
    (trace : MaterialTrace base scope start items final) (initial : Origin base scope prior start) :
    Origin base scope (prior ++ items) final := by
  induction trace generalizing prior with
  | nil => simpa only [List.append_nil] using initial
  | @cons current final item tail same licensed rest later =>
    have atItem : Origin base scope prior item.before.technology := same.symm ▸ initial
    simpa only [List.append_assoc, List.singleton_append] using
      later (Origin.advance base scope atItem licensed)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] in
def Released (state : M) : Prop := state.holder = none ∧ state.offered = none

theorem MaterialTrace.grant_after_release {start final : M} {items : List Item}
    (trace : MaterialTrace base scope start items final) (released : Released start)
    (candidate : Party) (holder : final.holder = some candidate) : LiveGrant base scope items candidate := by
  have noOrigin : Origin base scope [] start :=
    ⟨by simp [released.2], by simp [released.1]⟩
  exact (MaterialTrace.origin base scope trace noOrigin).grant candidate holder

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
