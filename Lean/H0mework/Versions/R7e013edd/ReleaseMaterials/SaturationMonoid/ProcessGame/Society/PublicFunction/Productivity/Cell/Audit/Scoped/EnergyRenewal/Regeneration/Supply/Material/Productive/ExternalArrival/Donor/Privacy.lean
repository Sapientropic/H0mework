import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Wire
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Privacy.SourceFunding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- The public six-unit permission exposes capacity in whole permitted lots, not its private residue. -/
def Capacity (left right : ℚ) : Prop := ∀ count : Nat, 6*(count:ℚ) ≤ left ↔ 6*(count:ℚ) ≤ right

theorem Capacity.six {left right : ℚ} (same : Capacity left right) : 6 ≤ left ↔ 6 ≤ right := by
  simpa using same 1

theorem Capacity.debit {left right : ℚ} (same : Capacity left right) : Capacity (left-6) (right-6) := by
  intro count
  have next := same (count+1)
  simp only [Nat.cast_add,Nat.cast_one,mul_add,mul_one] at next
  constructor
  · intro covered
    have prior : 6*(count:ℚ)+6 ≤ left := by linarith
    have other := next.mp prior
    linarith
  · intro covered
    have prior : 6*(count:ℚ)+6 ≤ right := by linarith
    have other := next.mpr prior
    linarith

theorem same_capacity_in_the_original_private_cell {left right : ℚ}
    (leftLower : 36≤left) (leftUpper : left<42) (rightLower : 36≤right) (rightUpper : right<42) : Capacity left right := by
  intro count
  by_cases covered : count≤6
  · have bound : (count:ℚ)≤6 := by exact_mod_cast covered
    exact iff_of_true (by linarith) (by linarith)
  · have bound : (7:ℚ)≤(count:ℚ) := by exact_mod_cast (show 7≤count by omega)
    exact iff_of_false (by linarith) (by linarith)

structure Related {lp rp : Plan} (left : State lp) (right : State rp) : Prop where
  legacy : ArrivalWirePrivacy.Related left.legacy right.legacy
  capacity : Capacity (Supply.Privacy.ownFrame left.legacy.service.session.current)
    (Supply.Privacy.ownFrame right.legacy.service.session.current)
  attempts : left.receipts.length = right.receipts.length

theorem status_public {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    status left.legacy.service round signer enabled (prepared left.legacy.service) =
      status right.legacy.service round signer enabled (prepared right.legacy.service) := by
  have twin := same.legacy.slots.material.session
  have funds : (quantity ≤ (prepared left.legacy.service).stock receiver .feed) ↔
      quantity ≤ (prepared right.legacy.service).stock receiver .feed := by
    exact same.capacity.six
  unfold status origin
  rw [←twin.current.round]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  simp only [not_congr funds]
  split
  · rfl
  · rename_i paid
    have secondStock : (6:ℚ)≤right.legacy.service.session.current.stock receiver .feed := by
      change ¬¬ (6:ℚ)≤right.legacy.service.session.current.stock receiver .feed at paid
      exact of_not_not paid
    have firstStock : (6:ℚ)≤left.legacy.service.session.current.stock receiver .feed := same.capacity.six.mpr secondStock
    have signerExact : signer=receiver := by
      by_contra wrong
      simp_all
    have firstPaid := DonorRelease.paid left.legacy.service.session.window.scope (prepared left.legacy.service) 6
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native])
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native]) (by norm_num) firstStock
    have secondPaid := DonorRelease.paid right.legacy.service.session.window.scope (prepared right.legacy.service) 6
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native])
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native]) (by norm_num) secondStock
    have firstValid : (Productive.law left.legacy.service.session.window.scope).Valid
        (prepared left.legacy.service) (request signer) := by
      simpa only [request,signerExact,quantity,DonorRelease.request] using firstPaid
    have secondValid : (Productive.law right.legacy.service.session.window.scope).Valid
        (prepared right.legacy.service) (request signer) := by
      simpa only [request,signerExact,quantity,DonorRelease.request] using secondPaid
    simp only [if_neg (not_not_intro firstValid),if_neg (not_not_intro secondValid)]

theorem supplied_is_the_original_six_unit_transfer {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool)
    (offered : status state round signer enabled (prepared state) = .supplied) :
    expected state round signer enabled = DonorRelease.after state.session.window.scope state.session.current 6 6 := by
  have source := Consumer.supplied_is_from_the_actual_funded_signer state round signer enabled _ offered
  unfold expected word
  rw [if_pos offered]
  unfold DonorRelease.after DonorRelease.word
  rw [if_pos (show DonorRelease.allowed 6 6 by simp [DonorRelease.allowed])]
  simp only [request,source.1,quantity,DonorRelease.request]
  rfl

theorem source_current_twin {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    Supply.Privacy.Twin (nextFinance left.legacy.service round signer enabled).session.current
      (nextFinance right.legacy.service round signer enabled).session.current := by
  have twin := same.legacy.slots.material.session
  have statuses := status_public same round signer enabled
  change Supply.Privacy.Twin (Runtime.current left.legacy.service round signer enabled)
    (Runtime.current right.legacy.service round signer enabled)
  rw [runtime_is_the_actual_word,runtime_is_the_actual_word]
  by_cases offered : status left.legacy.service round signer enabled (prepared left.legacy.service) = .supplied
  · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) = .supplied := statuses.symm.trans offered
    rw [supplied_is_the_original_six_unit_transfer _ _ _ _ offered,
      supplied_is_the_original_six_unit_transfer _ _ _ _ other,←twin.scope]
    have firstStock := (Consumer.supplied_is_from_the_actual_funded_signer _ _ _ _ _ offered).2.1
    have secondStock := (Consumer.supplied_is_from_the_actual_funded_signer _ _ _ _ _ other).2.1
    exact DonorRelease.after_twin twin.current _ rfl
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native])
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native]) 6 6 firstStock secondStock
  · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) ≠ .supplied := by rw [←statuses];exact offered
    simp only [expected,word,if_neg offered,if_neg other,←twin.scope]
    exact Productive.next_public (Productive.next_public twin.current _ rfl [] (by simp)) _ rfl [] (by simp)

theorem source_keeps_slot_count {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) :
    (nextFinance state round signer enabled).account.current.slots.length = state.account.current.slots.length := by
  have actual := Financial.Family.InstrumentProjection.first_two_visits_generate_their_own_slot_count
    Finance.sources (input state round signer enabled) state.account
  change (nextFinance state round signer enabled).account.current.slots.length = state.account.current.slots.length +
    ((Productive.law state.session.window.scope).rawItems (prepared state)
      (word state round signer enabled (prepared state))).countP
        (Financial.Family.InstrumentProjection.acceptedIssue (Productive.law state.session.window.scope)) at actual
  rw [actual]
  unfold word
  split <;> simp [RawLaw.rawItems,RawLaw.execute,Financial.Family.InstrumentProjection.acceptedIssue,request,DonorRelease.request]

theorem source_is_tracked {plan : Plan} (state : Finance.State plan) (old : ArrivalDeliveryLedger.Tracked state)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    ArrivalDeliveryLedger.Tracked (nextFinance state round signer enabled) := by
  have native : ArrivalDeliveryLedger.Contract (input state round signer enabled) := ⟨rfl,rfl⟩
  refine ⟨ArrivalDeliveryLedger.visits_keep_original_contracts _ native 0 2 state.account old.original,?_⟩
  change Financial.Family.ledgerClaims Finance.sources
    (Financial.Family.continueVisits Finance.sources (input state round signer enabled) 0 2 state.account).current .delivery =
    (Runtime.current state round signer enabled).claims .delivery
  rw [Runtime.current_is_own_root_next]
  exact Financial.Family.InstrumentProjection.continue_visits_source_slice Finance.sources (input state round signer enabled)
    0 2 state.account .delivery (ArrivalDeliveryLedger.compatible_with_the_original_admissions _ native state.account old.original) old.delivery

theorem donate_related {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    Related (donate left round signer enabled) (donate right round signer enabled) := by
  have twin := same.legacy.slots.material.session
  have next : Supply.Privacy.Source.SessionTwin (nextFinance left.legacy.service round signer enabled).session
      (nextFinance right.legacy.service round signer enabled).session :=
    ⟨source_current_twin same round signer enabled,twin.scope,twin.target,by
      simpa only [nextFinance,List.length_append,List.length_singleton] using congrArg (·+1) twin.history⟩
  refine ⟨⟨⟨⟨next,same.legacy.slots.material.spent⟩,?_⟩,
    source_is_tracked _ same.legacy.leftLedger round signer enabled,
    source_is_tracked _ same.legacy.rightLedger round signer enabled⟩,?_,by
      simpa only [donate,List.length_append,List.length_singleton] using congrArg (·+1) same.attempts⟩
  · change (nextFinance left.legacy.service round signer enabled).account.current.slots.length =
      (nextFinance right.legacy.service round signer enabled).account.current.slots.length
    rw [source_keeps_slot_count,source_keeps_slot_count]
    exact same.legacy.slots.slots
  · change Capacity (Supply.Privacy.ownFrame (nextFinance left.legacy.service round signer enabled).session.current)
      (Supply.Privacy.ownFrame (nextFinance right.legacy.service round signer enabled).session.current)
    have statuses := status_public same round signer enabled
    by_cases offered : status left.legacy.service round signer enabled (prepared left.legacy.service) = .supplied
    · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) = .supplied := statuses.symm.trans offered
      unfold Supply.Privacy.ownFrame
      rw [(Consumer.the_same_actual_occurrence_pays_and_delivers _ _ _ _ offered).1,
        (Consumer.the_same_actual_occurrence_pays_and_delivers _ _ _ _ other).1]
      exact same.capacity.debit
    · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) ≠ .supplied := by rw [←statuses];exact offered
      unfold Supply.Privacy.ownFrame
      rw [Consumer.refusal_does_not_create_a_payment_or_material _ _ _ _ offered,
        Consumer.refusal_does_not_create_a_payment_or_material _ _ _ _ other]
      exact same.capacity

theorem operate_related {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (command : Lean.Json) : Related (operate left command) (operate right command) := by
  refine ⟨ArrivalWirePrivacy.advance_related same.legacy command,?_,same.attempts⟩
  have frame {plan : Plan} (state : Consume.State plan) :
      Supply.Privacy.ownFrame (ExternalArrival.Wire.advance state command).service.session.current =
        Supply.Privacy.ownFrame state.service.session.current := by
    unfold ExternalArrival.Wire.advance
    cases ExternalArrival.Wire.eventOfJson command with
    | error _ => rfl
    | ok event => exact ArrivalBisimulation.step_keeps_own_private_frame state event
  change Capacity (Supply.Privacy.ownFrame (ExternalArrival.Wire.advance left.legacy command).service.session.current)
    (Supply.Privacy.ownFrame (ExternalArrival.Wire.advance right.legacy command).service.session.current)
  rw [frame,frame]
  exact same.capacity

theorem source_items_public {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    Productive.publicItems left.legacy.service.session.window.scope (prepared left.legacy.service)
      (word left.legacy.service round signer enabled (prepared left.legacy.service)) 0 =
    Productive.publicItems right.legacy.service.session.window.scope (prepared right.legacy.service)
      (word right.legacy.service round signer enabled (prepared right.legacy.service)) 0 := by
  have twin := same.legacy.slots.material.session
  have statuses := status_public same round signer enabled
  by_cases offered : status left.legacy.service round signer enabled (prepared left.legacy.service) = .supplied
  · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) = .supplied := statuses.symm.trans offered
    have first := Consumer.supplied_is_from_the_actual_funded_signer _ _ _ _ _ offered
    have second := Consumer.supplied_is_from_the_actual_funded_signer _ _ _ _ _ other
    have observation := DonorRelease.complete_observation_equal twin.current left.legacy.service.session.window.scope rfl
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native])
      (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native]) 6 6 first.2.1 second.2.1
    have items := congrArg Productive.Observation.actions observation
    simp only [word,if_pos offered,if_pos other]
    unfold prepared
    rw [←twin.scope]
    simpa only [DonorRelease.observe,DonorRelease.word,
      if_pos (show DonorRelease.allowed 6 6 by simp [DonorRelease.allowed]),
      request,quantity,first.1,DonorRelease.request,DonorRelease.prepared,Nat.cast_ofNat] using items
  · have other : status right.legacy.service round signer enabled (prepared right.legacy.service) ≠ .supplied := by rw [←statuses];exact offered
    simp only [word,if_neg offered,if_neg other,Productive.publicItems,Productive.execute,Productive.memo_exact,List.map_nil]

theorem render_public {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (command : Lean.Json) : Donor.Wire.render left command = Donor.Wire.render right command := by
  unfold Donor.Wire.render
  split
  · split
    · rfl
    · rename_i decoded
      rename_i round signer enabled
      have before := Productive.next_public same.legacy.slots.material.session.current
        left.legacy.service.session.window.scope rfl [] (by simp)
      have after := donate_related same round signer enabled
      have sources : Consume.sourceCurrent left.legacy = Consume.sourceCurrent right.legacy :=
        congrArg Packet.current same.legacy.slots.material.spent
      have nextSources : Consume.sourceCurrent (donate left round signer enabled).legacy =
          Consume.sourceCurrent (donate right round signer enabled).legacy :=
        congrArg Packet.current after.legacy.slots.material.spent
      have visibleBefore : Supply.Privacy.publicize (prepared left.legacy.service) =
          Supply.Privacy.publicize (prepared right.legacy.service) := by
        unfold prepared
        rw [←same.legacy.slots.material.session.scope]
        exact before.publicize
      have origins : origin left.legacy.service = origin right.legacy.service := same.legacy.slots.material.session.current.round
      have nextOrigins : origin (donate left round signer enabled).legacy.service =
          origin (donate right round signer enabled).legacy.service := after.legacy.slots.material.session.current.round
      simp only [status_public same round signer enabled,visibleBefore,
        after.legacy.slots.material.session.current.publicize,source_items_public same round signer enabled,
        origins,nextOrigins,
        sources,nextSources,after.legacy.slots.material.spent,
        ArrivalWirePrivacy.actual_wire_accounts_are_equal after.legacy]
  · exact ArrivalWirePrivacy.actual_wire_replies_are_equal same.legacy command

theorem advance_related {lp rp : Plan} {left : State lp} {right : State rp} (same : Related left right)
    (command : Lean.Json) : Related (Donor.Wire.advance left command) (Donor.Wire.advance right command) := by
  unfold Donor.Wire.advance
  split
  · cases parsed : Donor.Wire.decode command with
    | error _ => exact same
    | ok result => rcases result with ⟨round,signer,enabled⟩; exact donate_related same round signer enabled
  · exact operate_related same command

abbrev Strategy := List Lean.Json → Nat → Lean.Json

def play {plan : Plan} (initial : State plan) (strategy : Strategy) : Nat → State plan × List Lean.Json
  | 0 => (initial,[])
  | n+1 =>
    let previous := play initial strategy n
    let command := strategy previous.2 n
    (Donor.Wire.advance previous.1 command,previous.2++[Donor.Wire.render previous.1 command])

theorem every_adaptive_prefix_keeps_related_actual_successors_and_complete_output
    {lp rp : Plan} (left : State lp) (right : State rp) (same : Related left right)
    (strategy : Strategy) (count : Nat) :
    Related (play left strategy count).1 (play right strategy count).1 ∧
      (play left strategy count).2 = (play right strategy count).2 := by
  induction count with
  | zero => exact ⟨same,rfl⟩
  | succ n ih =>
    simp only [play,←ih.2]
    exact ⟨advance_related ih.1 _,by rw [render_public ih.1]⟩


theorem original_base_generates_the_donor_initial_relation (request : Lean.Json) :
    EnergyRenewal.Privacy.ResultRel
      (fun (left : ExternalArrival.Wire.Execution false) (right : ExternalArrival.Wire.Execution true) =>
        Related (start left.state) (start right.state) ∧ left.output=right.output)
      (ExternalArrival.Wire.execute false request) (ExternalArrival.Wire.execute true request) := by
  cases sourceRead : request.getObjVal? "source" with
  | error message =>
    simp only [ExternalArrival.Wire.execute,sourceRead,bind,Except.bind]
    exact .error message
  | ok source =>
    cases eventsRead : request.getObjValAs? (Array Lean.Json) "events" with
    | error message =>
      simp only [ExternalArrival.Wire.execute,sourceRead,eventsRead,bind,Except.bind]
      exact .error message
    | ok commands =>
      have original := ArrivalWirePrivacy.original_source_generates_the_wire_relation source
      cases left : History.restore false source [] with
      | error message =>
        cases right : History.restore true source [] with
        | error other =>
          rw [left,right] at original
          cases original
          simp only [ExternalArrival.Wire.execute,sourceRead,eventsRead,left,right,bind,Except.bind]
          exact .error message
        | ok _ => rw [left,right] at original;cases original
      | ok first =>
        cases right : History.restore true source [] with
        | error _ => rw [left,right] at original;cases original
        | ok second =>
          rw [left,right] at original
          cases original with
          | ok same =>
            have firstExecution := ArrivalWirePrivacy.original_execute_is_its_exact_fold false request source commands first sourceRead eventsRead left
            have secondExecution := ArrivalWirePrivacy.original_execute_is_its_exact_fold true request source commands second sourceRead eventsRead right
            have firstBound := SourceFunding.original_arrival_execution_is_backed false request _ firstExecution
            have secondBound := SourceFunding.original_arrival_execution_is_backed true request _ secondExecution
            dsimp only at firstBound secondBound
            rw [firstExecution,secondExecution]
            have all := ArrivalWirePrivacy.accumulated_json_words_are_equal (first.state,[]) (second.state,[]) same rfl commands.toList
            refine .ok ⟨⟨?_,?_,rfl⟩,?_⟩
            · change ArrivalWirePrivacy.Related
                (commands.foldl ArrivalWirePrivacy.accumulate (first.state,[])).1
                (commands.foldl ArrivalWirePrivacy.accumulate (second.state,[])).1
              simpa only [Array.foldl_toList] using all.1
            · change Capacity
                (Supply.Privacy.ownFrame (commands.foldl ArrivalWirePrivacy.accumulate (first.state,[])).1.service.session.current)
                (Supply.Privacy.ownFrame (commands.foldl ArrivalWirePrivacy.accumulate (second.state,[])).1.service.session.current)
              exact same_capacity_in_the_original_private_cell (by linarith [firstBound.1])
                (by linarith [firstBound.2]) (by linarith [secondBound.1]) (by linarith [secondBound.2])
            · simpa only [Array.foldl_toList] using all.2

def accumulate {plan : Plan} (prior : State plan × List Lean.Json) (command : Lean.Json) : State plan × List Lean.Json :=
  (Donor.Wire.advance prior.1 command,prior.2++[Donor.Wire.render prior.1 command])

theorem accumulated_words_have_equal_complete_outputs {lp rp : Plan}
    (left : State lp × List Lean.Json) (right : State rp × List Lean.Json)
    (same : Related left.1 right.1) (past : left.2=right.2) (commands : List Lean.Json) :
    Related (commands.foldl accumulate left).1 (commands.foldl accumulate right).1 ∧
      (commands.foldl accumulate left).2 = (commands.foldl accumulate right).2 := by
  induction commands generalizing left right with
  | nil => exact ⟨same,past⟩
  | cons command rest ih =>
    exact ih (accumulate left command) (accumulate right command) (advance_related same command)
      (by change left.2++[Donor.Wire.render left.1 command]=right.2++[Donor.Wire.render right.1 command]
          rw [past,render_public same command])

theorem original_donor_execute_is_its_exact_fold (larger : Bool) (request base : Lean.Json) (commands : Array Lean.Json)
    (first : ExternalArrival.Wire.Execution larger) (baseRead : request.getObjVal? "base"=.ok base)
    (commandsRead : request.getObjValAs? (Array Lean.Json) "commands"=.ok commands)
    (restored : ExternalArrival.Wire.execute larger base=.ok first) :
    Donor.Wire.execute larger request = .ok ⟨first.input,first.output,
      (commands.foldl accumulate (start first.state,[])).1,(commands.foldl accumulate (start first.state,[])).2⟩ := by
  simp only [Donor.Wire.execute,baseRead,commandsRead,restored,bind,Except.bind]
  change (forIn (m:=Except String) commands (start first.state,[]) (fun command previous =>
    pure (.yield (accumulate previous command)))).bind
    (fun result => pure (Donor.Wire.Execution.mk first.input first.output result.1 result.2)) = _
  rw [Array.forIn_pure_yield_eq_foldl]
  rfl

def ExecutionRelated (left : Donor.Wire.Execution false) (right : Donor.Wire.Execution true) : Prop :=
  left.old=right.old ∧ left.output=right.output ∧ Related left.state right.state

theorem original_source_generates_the_complete_donor_execution_relation (request : Lean.Json) :
    EnergyRenewal.Privacy.ResultRel ExecutionRelated
      (Donor.Wire.execute false request) (Donor.Wire.execute true request) := by
  cases baseRead : request.getObjVal? "base" with
  | error message =>
    simp only [Donor.Wire.execute,baseRead,bind,Except.bind]
    exact .error message
  | ok base =>
    have original := original_base_generates_the_donor_initial_relation base
    cases left : ExternalArrival.Wire.execute false base with
    | error message =>
      cases right : ExternalArrival.Wire.execute true base with
      | error other =>
        rw [left,right] at original
        cases original
        simp only [Donor.Wire.execute,baseRead,left,right,bind,Except.bind]
        exact .error message
      | ok _ => rw [left,right] at original;cases original
    | ok first =>
      cases right : ExternalArrival.Wire.execute true base with
      | error _ => rw [left,right] at original;cases original
      | ok second =>
        rw [left,right] at original
        cases original with
        | ok same =>
          cases commandsRead : request.getObjValAs? (Array Lean.Json) "commands" with
          | error message =>
            simp only [Donor.Wire.execute,baseRead,left,right,commandsRead,bind,Except.bind]
            exact .error message
          | ok commands =>
            rw [original_donor_execute_is_its_exact_fold false request base commands first baseRead commandsRead left,
              original_donor_execute_is_its_exact_fold true request base commands second baseRead commandsRead right]
            have all := accumulated_words_have_equal_complete_outputs (start first.state,[]) (start second.state,[]) same.1 rfl commands.toList
            exact .ok ⟨same.2,by simpa only [Array.foldl_toList] using all.2,
              by simpa only [Array.foldl_toList] using all.1⟩

theorem complete_original_donor_readouts_are_equal (request : Lean.Json) :
    Donor.Wire.readout false request=Donor.Wire.readout true request := by
  have original := original_source_generates_the_complete_donor_execution_relation request
  unfold Donor.Wire.readout
  cases left : Donor.Wire.execute false request with
  | error message =>
    cases right : Donor.Wire.execute true request with
    | error other => rw [left,right] at original;cases original;rfl
    | ok _ => rw [left,right] at original;cases original
  | ok first =>
    cases right : Donor.Wire.execute true request with
    | error _ => rw [left,right] at original;cases original
    | ok second =>
      rw [left,right] at original
      cases original with
      | ok same =>
        have source : Consume.sourceCurrent first.state.legacy=Consume.sourceCurrent second.state.legacy :=
          congrArg Packet.current same.2.2.legacy.slots.material.spent
        simp only [bind,Except.bind,same.1,same.2.1,
          ArrivalWirePrivacy.actual_state_json_is_equal same.2.2.legacy.slots.material.session.current,
          source,same.2.2.legacy.slots.material.spent,same.2.2.attempts,
          ArrivalWirePrivacy.actual_wire_accounts_are_equal same.2.2.legacy]

def commands {plan : Plan} (initial : State plan) (strategy : Strategy) : Nat → List Lean.Json
  | 0 => []
  | n+1 => commands initial strategy n ++ [strategy (play initial strategy n).2 n]

theorem play_is_the_actual_emitted_word {plan : Plan} (initial : State plan) (strategy : Strategy) (count : Nat) :
    play initial strategy count = (commands initial strategy count).foldl accumulate (initial,[]) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [commands,List.foldl_append,List.foldl_cons,List.foldl_nil,←ih]
    rfl

theorem related_policies_emit_the_same_commands {lp rp : Plan} (left : State lp) (right : State rp)
    (same : Related left right) (strategy : Strategy) (count : Nat) :
    commands left strategy count = commands right strategy count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [commands,commands,ih,
      (every_adaptive_prefix_keeps_related_actual_successors_and_complete_output left right same strategy n).2]

def adaptiveExecute (larger : Bool) (base : Lean.Json) (strategy : Strategy) (count : Nat) :
    Except String (Donor.Wire.Execution larger × List Lean.Json) := do
  let original ← ExternalArrival.Wire.execute larger base
  let initial := start original.state
  let final := play initial strategy count
  return (⟨original.input,original.output,final.1,final.2⟩,commands initial strategy count)

theorem the_original_source_generates_every_adaptive_donor_relation (base : Lean.Json)
    (strategy : Strategy) (count : Nat) :
    EnergyRenewal.Privacy.ResultRel
      (fun (left : Donor.Wire.Execution false × List Lean.Json) (right : Donor.Wire.Execution true × List Lean.Json) =>
        ExecutionRelated left.1 right.1 ∧ left.2=right.2)
      (adaptiveExecute false base strategy count) (adaptiveExecute true base strategy count) := by
  have original := original_base_generates_the_donor_initial_relation base
  unfold adaptiveExecute
  cases left : ExternalArrival.Wire.execute false base with
  | error message =>
    cases right : ExternalArrival.Wire.execute true base with
    | error other => rw [left,right] at original;cases original;exact .error message
    | ok _ => rw [left,right] at original;cases original
  | ok first =>
    cases right : ExternalArrival.Wire.execute true base with
    | error _ => rw [left,right] at original;cases original
    | ok second =>
      rw [left,right] at original
      cases original with
      | ok same =>
        have generated := every_adaptive_prefix_keeps_related_actual_successors_and_complete_output
          (start first.state) (start second.state) same.1 strategy count
        exact .ok ⟨⟨same.2,generated.2,generated.1⟩,
          related_policies_emit_the_same_commands (start first.state) (start second.state) same.1 strategy count⟩

def request (base : Lean.Json) (word : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("base",base),("commands",Lean.Json.arr word.toArray)]

theorem request_base (base : Lean.Json) (word : List Lean.Json) :
    (request base word).getObjVal? "base" = .ok base := rfl

theorem request_commands (base : Lean.Json) (word : List Lean.Json) :
    (request base word).getObjValAs? (Array Lean.Json) "commands" = .ok word.toArray := by
  change word.toArray.mapM (fun value => Except.ok value) = Except.ok word.toArray
  simpa only [id_eq,pure,Except.pure,Array.map_id] using
    (Array.mapM_pure (m:=Except String) (xs:=word.toArray) (f:=id))

theorem every_generated_policy_word_is_consumed_by_the_original_wire (larger : Bool)
    (base : Lean.Json) (strategy : Strategy) (count : Nat)
    (execution : Donor.Wire.Execution larger × List Lean.Json)
    (generated : adaptiveExecute larger base strategy count = .ok execution) :
    Donor.Wire.execute larger (request base execution.2) = .ok execution.1 := by
  unfold adaptiveExecute at generated
  cases original : ExternalArrival.Wire.execute larger base with
  | error message => simp only [original,bind,Except.bind] at generated;contradiction
  | ok first =>
    simp only [original,bind,Except.bind] at generated
    cases Except.ok.inj generated
    rw [original_donor_execute_is_its_exact_fold larger _ base _ first
      (request_base base _) (request_commands base _) original]
    rw [List.foldl_toArray,←play_is_the_actual_emitted_word]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy
