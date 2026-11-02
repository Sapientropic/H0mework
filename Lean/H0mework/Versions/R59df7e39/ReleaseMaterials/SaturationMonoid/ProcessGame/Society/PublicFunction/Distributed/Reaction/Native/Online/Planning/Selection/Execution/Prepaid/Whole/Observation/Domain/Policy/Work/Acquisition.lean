import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Checks
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
namespace CollectionAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}

variable (prepared : Prepared input) (reference : Section prepared) (order : List (Section prepared))
def step (prepared : Prepared input) := 2*Checks.noWorseWeight prepared+4
inductive State where
  | walking (remaining : List (Section prepared))
      (wrap : Pool prepared reference remaining → Pool prepared reference order)
      (coherent : wrap (collect prepared reference remaining) = collect prepared reference order)
  | testing (head : Section prepared) (tail : List (Section prepared))
      (wrap : Pool prepared reference (head::tail) → Pool prepared reference order)
      (coherent : wrap (collect prepared reference (head::tail)) = collect prepared reference order)
      (cursor : Checks.State (Checks.noWorseCode head reference))
  | checked (head : Section prepared) (tail : List (Section prepared))
      (wrap : Pool prepared reference (head::tail) → Pool prepared reference order)
      (coherent : wrap (collect prepared reference (head::tail)) = collect prepared reference order)
      (checked : Check prepared (NoWorse prepared head reference)) (actual : checked = noWorse prepared head reference)
  | finished (pool : Pool prepared reference order) (generated : pool = collect prepared reference order)
def initial : State prepared reference order := .walking order id rfl
inductive Event where
  | opened (head : Section prepared)
  | test (head : Section prepared) (event : Checks.Event (Checks.noWorseCode head reference))
  | checked (head : Section prepared) (check : Check prepared (NoWorse prepared head reference)) (actual : check = noWorse prepared head reference)
  | retained (head : Section prepared) (value : Bool)
  | completed (pool : Pool prepared reference order) (generated : pool = collect prepared reference order)
def move : State prepared reference order → Option (State prepared reference order × Event prepared reference order)
  | .walking [] wrap coherent => some (.finished (wrap Builders.collectNil) coherent,.completed (wrap Builders.collectNil) coherent)
  | .walking (head::tail) wrap coherent =>
      some (.testing head tail wrap coherent (Checks.initial (Checks.noWorseCode head reference)),.opened head)
  | .testing head tail wrap coherent (.finished checked generated) =>
      let actual := generated.trans (Checks.noWorseCode_exact head reference)
      some (.checked head tail wrap coherent checked actual,.checked head checked actual)
  | .testing head tail wrap coherent cursor@(.evaluating ..) | .testing head tail wrap coherent cursor@(.returning ..) =>
      match _step : Checks.move (Checks.noWorseCode head reference) cursor with
      | none => none
      | some (after,event) => some (.testing head tail wrap coherent after,.test head event)
  | .checked head tail wrap coherent checked actual =>
      some (.walking tail (fun later => wrap (Builders.collectCons head tail checked later)) (by
        rw [Builders.collectCons_exact head tail checked actual];exact coherent),.retained head checked.value)
  | .finished .. => none
def State.rank : State prepared reference order → Nat
  | .walking remaining .. => remaining.length*step prepared+1
  | .testing head tail _ _ cursor => tail.length*step prepared+cursor.rank (Checks.noWorseCode head reference)+3
  | .checked _ tail .. => tail.length*step prepared+2
  | .finished .. => 0
def State.done : State prepared reference order → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared reference order} {event : Event prepared reference order}
    (actual : move prepared reference order before = some (after,event)) : after.rank prepared reference order < before.rank prepared reference order := by
  cases before with
  | walking remaining =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons,Checks.initial,Checks.State.rank,Checks.Kont.weight,Checks.noWorseCode_weight,step,Nat.add_mul,Nat.one_mul];omega
  | testing head tail wrap coherent cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Checks.State.rank];omega
      | evaluating | returning =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Checks.progress (Checks.noWorseCode head reference) step;simp only [State.rank];omega)
  | checked => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared reference order) : move prepared reference order before = none ↔ before.done prepared reference order = true := by
  cases before with
  | walking remaining => cases remaining <;> simp [move,State.done]
  | testing head tail wrap coherent cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | evaluating | returning =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Checks.no_move_iff_done (Checks.noWorseCode head reference) _).mp stopped;cases done)
            | simp
  | checked | finished => simp [move,State.done]
end CollectionAcquisition
namespace ScanAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}

variable (prepared : Prepared input) (reference : Section prepared) (first : Candidate prepared reference) (original : List (Candidate prepared reference))
def step (prepared : Prepared input) := 2*Checks.strictWeight prepared+4
inductive State where
  | walking (pivot : Candidate prepared reference) (remaining : List (Candidate prepared reference))
      (wrap : Builders.ScanValue pivot remaining → Builders.ScanValue first original)
      (coherent : wrap (Builders.scanSpecification pivot remaining) = Builders.scanSpecification first original)
  | testing (pivot head : Candidate prepared reference) (tail : List (Candidate prepared reference))
      (wrap : Builders.ScanValue pivot (head::tail) → Builders.ScanValue first original)
      (coherent : wrap (Builders.scanSpecification pivot (head::tail)) = Builders.scanSpecification first original)
      (cursor : Checks.State (Checks.strictCode pivot.term head.term))
  | checked (pivot head : Candidate prepared reference) (tail : List (Candidate prepared reference))
      (wrap : Builders.ScanValue pivot (head::tail) → Builders.ScanValue first original)
      (coherent : wrap (Builders.scanSpecification pivot (head::tail)) = Builders.scanSpecification first original)
      (checked : Check prepared (Strict prepared pivot.term head.term)) (actual : checked = strict prepared pivot.term head.term)
  | finished (found : Builders.ScanValue first original) (generated : found = Builders.scanSpecification first original)
def initial : State prepared reference first original := .walking first original id rfl
inductive Event where
  | opened (pivot head : Candidate prepared reference)
  | test (pivot head : Candidate prepared reference) (event : Checks.Event (Checks.strictCode pivot.term head.term))
  | checked (pivot head : Candidate prepared reference) (check : Check prepared (Strict prepared pivot.term head.term)) (actual : check = strict prepared pivot.term head.term)
  | selected (pivot head : Candidate prepared reference) (replaced : Bool)
  | completed (found : Builders.ScanValue first original) (generated : found = Builders.scanSpecification first original)
def move : State prepared reference first original → Option (State prepared reference first original × Event prepared reference first original)
  | .walking pivot [] wrap coherent => some (.finished (wrap (Builders.scanNil pivot)) coherent,.completed (wrap (Builders.scanNil pivot)) coherent)
  | .walking pivot (head::tail) wrap coherent =>
      some (.testing pivot head tail wrap coherent (Checks.initial (Checks.strictCode pivot.term head.term)),.opened pivot head)
  | .testing pivot head tail wrap coherent (.finished checked generated) =>
      let actual := generated.trans (Checks.strictCode_exact pivot.term head.term)
      some (.checked pivot head tail wrap coherent checked actual,.checked pivot head checked actual)
  | .testing pivot head tail wrap coherent cursor@(.evaluating ..) | .testing pivot head tail wrap coherent cursor@(.returning ..) =>
      match _step : Checks.move (Checks.strictCode pivot.term head.term) cursor with
      | none => none
      | some (after,event) => some (.testing pivot head tail wrap coherent after,.test pivot head event)
  | .checked pivot head tail wrap coherent checked actual => match decision : checked.decision with
    | .isTrue better =>
        some (.walking head tail (fun later => wrap (Builders.scanBetter pivot head tail checked better later)) (by
          rw [Builders.scanBetter_exact pivot head tail checked actual better decision];exact coherent),.selected pivot head true)
    | .isFalse notBetter =>
        some (.walking pivot tail (fun later => wrap (Builders.scanKept pivot head tail checked notBetter later)) (by
          rw [Builders.scanKept_exact pivot head tail checked actual notBetter decision];exact coherent),.selected pivot head false)
  | .finished .. => none
def State.rank : State prepared reference first original → Nat
  | .walking _ remaining .. => remaining.length*step prepared+1
  | .testing pivot head tail _ _ cursor => tail.length*step prepared+cursor.rank (Checks.strictCode pivot.term head.term)+3
  | .checked _ _ tail .. => tail.length*step prepared+2
  | .finished .. => 0
def State.done : State prepared reference first original → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared reference first original} {event : Event prepared reference first original}
    (actual : move prepared reference first original before = some (after,event)) : after.rank prepared reference first original < before.rank prepared reference first original := by
  cases before with
  | walking pivot remaining =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons,Checks.initial,Checks.State.rank,Checks.Kont.weight,Checks.strictCode_weight,step,Nat.add_mul,Nat.one_mul];omega
  | testing pivot head tail wrap coherent cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Checks.State.rank];omega
      | evaluating | returning =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Checks.progress (Checks.strictCode pivot.term head.term) step;simp only [State.rank];omega)
  | checked =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared reference first original) : move prepared reference first original before = none ↔ before.done prepared reference first original = true := by
  cases before with
  | walking pivot remaining => cases remaining <;> simp [move,State.done]
  | testing pivot head tail wrap coherent cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | evaluating | returning =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Checks.no_move_iff_done (Checks.strictCode pivot.term head.term) _).mp stopped;cases done)
            | simp
  | checked => dsimp only [move,State.done];split <;> simp
  | finished => simp [move,State.done]
end ScanAcquisition
namespace CompilationAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}

def afterCollection (prepared : Prepared input) (reference : Section prepared) := (collect prepared reference (sections prepared)).accepted.length*ScanAcquisition.step prepared+3
private theorem afterCollection_exact (pool : Pool prepared reference (sections prepared)) (generated : pool = collect prepared reference (sections prepared)) :
    afterCollection prepared reference = pool.accepted.length*ScanAcquisition.step prepared+3 := by cases generated;rfl
inductive State (prepared : Prepared input) (reference : Section prepared) where
  | collection (cursor : CollectionAcquisition.State prepared reference (sections prepared))
  | scanning (pool : Pool prepared reference (sections prepared)) (generated : pool = collect prepared reference (sections prepared))
      (head : Candidate prepared reference) (tail : List (Candidate prepared reference)) (same : pool.accepted = head::tail)
      (cursor : ScanAcquisition.State prepared reference head tail)
  | finished (made : Compilation prepared reference) (generated : made = compile prepared reference)
def initial (prepared : Prepared input) (reference : Section prepared) : State prepared reference := .collection (CollectionAcquisition.initial prepared reference (sections prepared))
inductive Event (prepared : Prepared input) (reference : Section prepared) where
  | collection (event : CollectionAcquisition.Event prepared reference (sections prepared))
  | collected (pool : Pool prepared reference (sections prepared)) (generated : pool = collect prepared reference (sections prepared))
  | scan (pool : Pool prepared reference (sections prepared)) (head : Candidate prepared reference) (tail : List (Candidate prepared reference))
      (event : ScanAcquisition.Event prepared reference head tail)
  | completed (made : Compilation prepared reference) (generated : made = compile prepared reference)
def move : State prepared reference → Option (State prepared reference × Event prepared reference)
  | .collection (.finished pool generated) => match same : pool.accepted with
    | [] =>
        let made := Builders.compileEmpty pool same
        let exact := Builders.compileEmpty_exact pool generated same
        some (.finished made exact,.completed made exact)
    | head::tail => some (.scanning pool generated head tail same (ScanAcquisition.initial prepared reference head tail),.collected pool generated)
  | .collection cursor@(.walking ..) | .collection cursor@(.testing ..) | .collection cursor@(.checked ..) =>
      match _step : CollectionAcquisition.move prepared reference (sections prepared) cursor with
      | none => none
      | some (after,event) => some (.collection after,.collection event)
  | .scanning pool generated head tail same (.finished found actual) =>
      let made := Builders.compileSelected pool head tail same found
      let exact := Builders.compileSelected_exact pool generated head tail same found actual
      some (.finished made exact,.completed made exact)
  | .scanning pool generated head tail same cursor@(.walking ..) | .scanning pool generated head tail same cursor@(.testing ..) | .scanning pool generated head tail same cursor@(.checked ..) =>
      match _step : ScanAcquisition.move prepared reference head tail cursor with
      | none => none
      | some (after,event) => some (.scanning pool generated head tail same after,.scan pool head tail event)
  | .finished .. => none
def State.rank : State prepared reference → Nat
  | .collection cursor => cursor.rank prepared reference (sections prepared)+afterCollection prepared reference+2
  | .scanning _ _ head tail _ cursor => cursor.rank prepared reference head tail+1
  | .finished .. => 0
def State.done : State prepared reference → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared reference} {event : Event prepared reference}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | collection cursor =>
      cases cursor with
      | finished pool generated =>
          dsimp only [move] at actual;split at actual
          · cases Option.some.inj actual;simp only [State.rank,CollectionAcquisition.State.rank];omega
          · rename_i head tail same;cases Option.some.inj actual
            simp only [State.rank,CollectionAcquisition.State.rank,ScanAcquisition.initial,ScanAcquisition.State.rank,afterCollection_exact pool generated,same,List.length_cons,Nat.add_mul,Nat.one_mul];omega
      | walking | testing | checked =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := CollectionAcquisition.progress prepared reference (sections prepared) step;simp only [State.rank];omega)
  | scanning pool generated head tail same cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,ScanAcquisition.State.rank];omega
      | walking | testing | checked =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := ScanAcquisition.progress prepared reference head tail step;simp only [State.rank];omega)
  | finished => cases actual
theorem no_move_iff_done (before : State prepared reference) : move before = none ↔ before.done = true := by
  cases before with
  | collection cursor =>
      cases cursor with
      | finished => dsimp only [move,State.done];split <;> simp
      | walking | testing | checked =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (CollectionAcquisition.no_move_iff_done prepared reference (sections prepared) _).mp stopped;cases done)
            | simp
  | scanning pool generated head tail same cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | walking | testing | checked =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (ScanAcquisition.no_move_iff_done prepared reference head tail _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end CompilationAcquisition
namespace ReceiptAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}

def rejectionStep (prepared : Prepared input) := 2*(rows prepared).length+4
def openingRank (prepared : Prepared input) := 2*Checks.verifyWeight prepared+(sections prepared).length*rejectionStep prepared+5
variable (made : Compilation prepared reference)
inductive State where
  | opening
  | openingKnown (compiled : made = compile prepared reference)
  | rejectingKnown (compiled : made = compile prepared reference)
      (rejected : (term : Section prepared) → Rejected prepared reference term) (same : made.result = .blocked rejected)
      (cached : List (Operation prepared)) (remaining : List (Section prepared))
      (conserved : cached++remaining.flatMap (fun term => (rejected term).work) = (sections prepared).flatMap (fun term => (rejected term).work))
  | rejection (compiled : made = compile prepared reference)
      (rejected : (term : Section prepared) → Rejected prepared reference term) (same : made.result = .blocked rejected)
      (cached : List (Operation prepared)) (head : Section prepared) (tail : List (Section prepared))
      (conserved : cached++(head::tail).flatMap (fun term => (rejected term).work) = (sections prepared).flatMap (fun term => (rejected term).work))
      (cursor : Checks.Rejection.State reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head))
  | verifying (choice : Choice prepared reference) (same : made.result = .selected choice)
      (cursor : Checks.State (Checks.verifyCode reference choice.policy.term))
  | rejecting (rejected : (term : Section prepared) → Rejected prepared reference term) (same : made.result = .blocked rejected)
      (cached : List (Operation prepared)) (remaining : List (Section prepared))
      (conserved : cached++remaining.flatMap (fun term => (rejected term).work) = (sections prepared).flatMap (fun term => (rejected term).work))
  | reviewing (review : Check prepared (Reviewed prepared made.result)) (generated : review = inspect prepared made)
  | finished (receipt : Receipt prepared made) (generated : receipt = certify prepared made)
def initial : State made := .opening
def initialKnown (compiled : made = compile prepared reference) : State made := .openingKnown compiled
inductive Event where
  | opened
  | rejectionStep (rejected : (term : Section prepared) → Rejected prepared reference term) (head : Section prepared)
      (event : Checks.Rejection.Event reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head))
  | verification (choice : Choice prepared reference) (event : Checks.Event (Checks.verifyCode reference choice.policy.term))
  | rejected (term : Section prepared) (report : Rejected prepared reference term)
  | reviewed (review : Check prepared (Reviewed prepared made.result)) (generated : review = inspect prepared made)
  | completed (receipt : Receipt prepared made) (generated : receipt = certify prepared made)
def move : State made → Option (State made × Event made)
  | .openingKnown compiled => match same : made.result with
    | .selected choice => some (.verifying choice same (Checks.initial (Checks.verifyCode reference choice.policy.term)),.opened)
    | .blocked rejected => some (.rejectingKnown compiled rejected same [] (sections prepared) rfl,.opened)
  | .rejectingKnown compiled rejected same cached (head::tail) conserved =>
      some (.rejection compiled rejected same cached head tail conserved
        (Checks.Rejection.initial reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head)),.opened)
  | .rejectingKnown _ rejected same cached [] conserved =>
      let review := Builders.blockedReview made rejected same cached
      let exact := Builders.blockedReview_exact made rejected same cached (by simpa only [List.flatMap_nil,List.append_nil] using conserved)
      some (.reviewing review exact,.reviewed review exact)
  | .rejection compiled rejected same cached head tail conserved (.finished report generated) =>
      have actual : report = rejected head := generated.trans (Builders.canonicalRejected made compiled rejected same head).symm
      some (.rejectingKnown compiled rejected same (cached++report.work) tail (by
        rw [actual];simpa only [List.flatMap_cons,List.append_assoc] using conserved),.rejected head report)
  | .rejection compiled rejected same cached head tail conserved cursor@(.walking ..) | .rejection compiled rejected same cached head tail conserved cursor@(.checked ..) =>
      match _step : Checks.Rejection.move reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head) cursor with
      | none => none
      | some (after,event) => some (.rejection compiled rejected same cached head tail conserved after,.rejectionStep rejected head event)
  | .opening => match same : made.result with
    | .selected choice => some (.verifying choice same (Checks.initial (Checks.verifyCode reference choice.policy.term)),.opened)
    | .blocked rejected => some (.rejecting rejected same [] (sections prepared) rfl,.opened)
  | .verifying choice same (.finished checked generated) =>
      let review := Builders.selectedFromChecked made choice same checked
      let exact := Builders.selectedFromChecked_exact made choice same checked (generated.trans (Checks.verifyCode_exact reference choice.policy.term))
      some (.reviewing review exact,.reviewed review exact)
  | .verifying choice same cursor@(.evaluating ..) | .verifying choice same cursor@(.returning ..) =>
      match _step : Checks.move (Checks.verifyCode reference choice.policy.term) cursor with
      | none => none
      | some (after,event) => some (.verifying choice same after,.verification choice event)
  | .rejecting rejected same cached (head::tail) conserved =>
      let report := rejected head
      some (.rejecting rejected same (cached++report.work) tail (by
        simpa only [List.flatMap_cons,List.append_assoc] using conserved),.rejected head report)
  | .rejecting rejected same cached [] conserved =>
      let review := Builders.blockedReview made rejected same cached
      let exact := Builders.blockedReview_exact made rejected same cached (by simpa only [List.flatMap_nil,List.append_nil] using conserved)
      some (.reviewing review exact,.reviewed review exact)
  | .reviewing review generated =>
      let receipt := Builders.receiptFrom made review generated
      let exact := Builders.receiptFrom_exact made review generated
      some (.finished receipt exact,.completed receipt exact)
  | .finished .. => none
def State.rank : State made → Nat
  | .opening | .openingKnown _ => openingRank prepared
  | .rejectingKnown _ _ _ _ remaining _ => remaining.length*rejectionStep prepared+2
  | .rejection _ rejected _ _ head tail _ cursor => tail.length*rejectionStep prepared+
      cursor.rank reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head)+3
  | .verifying choice _ cursor => cursor.rank (Checks.verifyCode reference choice.policy.term)+2
  | .rejecting _ _ _ remaining _ => remaining.length+2
  | .reviewing .. => 1
  | .finished .. => 0
def State.done : State made → Bool | .finished .. => true | _ => false
theorem progress {before after : State made} {event : Event made}
    (actual : move made before = some (after,event)) : after.rank made < before.rank made := by
  cases before with
  | opening | openingKnown =>
      have sized : (sections prepared).length ≤ (sections prepared).length*rejectionStep prepared := by
        have lower : 1 ≤ rejectionStep prepared := by unfold rejectionStep;omega
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (sections prepared).length lower
      simp only [rejectionStep] at sized
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank,Checks.initial,Checks.State.rank,Checks.Kont.weight,Checks.verifyCode_weight,openingRank,rejectionStep];omega
  | rejectingKnown compiled rejected same cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,Checks.Rejection.initial,Checks.Rejection.State.rank,List.length_cons,rejectionStep,Nat.add_mul,Nat.one_mul];omega
  | rejection compiled rejected same cached head tail conserved cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Checks.Rejection.State.rank];omega
      | walking | checked =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Checks.Rejection.progress reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head) step
               simp only [State.rank];omega)
  | verifying choice same cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Checks.State.rank];omega
      | evaluating | returning =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Checks.progress (Checks.verifyCode reference choice.policy.term) step;simp only [State.rank];omega)
  | rejecting rejected same cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons];omega
  | reviewing => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State made) : move made before = none ↔ before.done made = true := by
  cases before with
  | opening | openingKnown => dsimp only [move,State.done];split <;> simp
  | rejectingKnown compiled rejected same cached remaining conserved => cases remaining <;> simp [move,State.done]
  | rejection compiled rejected same cached head tail conserved cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | walking | checked =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Checks.Rejection.no_move_iff_done reference head (rows prepared) (fun _ listed => listed) (Builders.rejectedInvalid rejected head) _).mp stopped;cases done)
            | simp
  | verifying choice same cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | evaluating | returning =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Checks.no_move_iff_done (Checks.verifyCode reference choice.policy.term) _).mp stopped;cases done)
            | simp
  | rejecting rejected same cached remaining conserved => cases remaining <;> simp [move,State.done]
  | reviewing | finished => simp [move,State.done]
end ReceiptAcquisition

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
