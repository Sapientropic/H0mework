import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LifecycleJoint

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

private def transportCandidateGrant
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) : Mandate.Grant base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact grant

private theorem transport_candidate_event
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent; cases sameWord; rfl

private theorem transport_candidate_items
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).proposal.item.val = grant.proposal.item.val ∧
      (transportCandidateGrant sameCurrent sameWord grant).acceptance.item.val = grant.acceptance.item.val := by
  cases sameCurrent; cases sameWord; exact ⟨rfl, rfl⟩

private theorem transport_candidate_initial
    {oldCurrent newCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {oldWord newWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (birth : Nat) (sameCurrent : newCurrent birth = oldCurrent birth) (sameWord : newWord birth = oldWord birth)
    (grant : Mandate.Grant base scope (oldCurrent birth) (oldWord birth)) :
    Mandate.Lifecycle.Observed.initialState base scope newCurrent newWord birth
        (transportCandidateGrant sameCurrent sameWord grant) =
      Mandate.Lifecycle.Observed.initialState base scope oldCurrent oldWord birth grant := by
  change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent).target = _
  rw [transport_candidate_event]
  rfl

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
  (term : Cut.Term bound.source input cut)
  (active : bound.source.feedback? = some input) (empty : bound.source.continuation = [])

include active empty in
private theorem candidate_current (visit : Nat) (inside : visit ≤ terminalDepth bound input cut) :
    Native.Authority.currentAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) visit =
      Native.Authority.currentAt (candidate bound input cut rival term) visit :=
  Future.joint_current bound.source input cut rival term.val active empty term.property (visit + 1)
    (by dsimp only [terminalDepth, Cut.finish, Cut.start, Cut.horizon] at *; omega)

include active empty in
private theorem candidate_word (visit : Nat) (inside : visit ≤ terminalDepth bound input cut) :
    Native.Authority.wordAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) visit =
      Native.Authority.wordAt (candidate bound input cut rival term) visit :=
  (Future.joint_occurrences bound.source input cut rival term.val active empty term.property (visit + 1)
    (by dsimp only [terminalDepth, Cut.finish, Cut.start, Cut.horizon] at *; omega)).2

include active empty in
private theorem candidate_grant_image (birth : Nat) (inside : birth ≤ terminalDepth bound input cut)
    (grant : Mandate.Grant bound.base bound.scope
      (Native.Authority.currentAt (candidate bound input cut rival term) birth)
      (Native.Authority.wordAt (candidate bound input cut rival term) birth)) :
    grantImage (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) birth
        (terminalDepth bound input cut) (Native.Authority.traceGrant _ _ _
          (transportCandidateGrant (candidate_current bound input cut rival term active empty birth inside)
            (candidate_word bound input cut rival term active empty birth inside) grant)) =
      grantImage (candidate bound input cut rival term) birth (terminalDepth bound input cut)
        (Native.Authority.traceGrant _ _ _ grant) := by
  have items := transport_candidate_items
    (candidate_current bound input cut rival term active empty birth inside)
    (candidate_word bound input cut rival term active empty birth inside) grant
  have initial := transport_candidate_initial birth
    (candidate_current bound input cut rival term active empty birth inside)
    (candidate_word bound input cut rival term active empty birth inside) grant
  have index := congrArg ExecutionItem.index items.2
  have state := Mandate.Lifecycle.Observed.through_state_congr (terminalDepth bound input cut) index initial
    (candidate_current bound input cut rival term active empty) (candidate_word bound input cut rival term active empty)
  have final := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have history := grant_through_images_congr bound.source.code (terminalDepth bound input cut) index initial
    (candidate_current bound input cut rival term active empty) (candidate_word bound input cut rival term active empty)
  have election := transport_candidate_event
    (candidate_current bound input cut rival term active empty birth inside)
    (candidate_word bound input cut rival term active empty birth inside) grant
  have original := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl, congrArg (itemImage bound.source.code) items.1, congrArg (itemImage bound.source.code) items.2,
    congrArg grantObligationImage original, congrArg grantObligationImage final, history⟩

private theorem grantsAt_transport
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord) :
    Mandate.grantsAt base scope second secondWord =
      (Mandate.grantsAt base scope first firstWord).map (transportCandidateGrant sameCurrent sameWord) := by
  cases sameCurrent; cases sameWord
  exact (List.map_id _).symm

include active empty in
theorem joint_candidate_grant_manifest :
    (generate bound input cut (Future.jointOpponent bound.source input cut rival) term active).candidateGrants =
      (generate bound input cut rival term active).candidateGrants := by
  simp only [generate, Native.Authority.recordsAt, List.map_flatMap, List.map_map, Function.comp_def]
  apply congrArg (List.flatMap · (List.finRange (terminalDepth bound input cut + 1)))
  funext birth
  have inside : birth.val ≤ terminalDepth bound input cut := Nat.le_of_lt_succ birth.isLt
  rw [grantsAt_transport (candidate_current bound input cut rival term active empty birth.val inside)
    (candidate_word bound input cut rival term active empty birth.val inside)]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro grant _
  exact candidate_grant_image bound input cut rival term active empty birth.val inside grant

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
