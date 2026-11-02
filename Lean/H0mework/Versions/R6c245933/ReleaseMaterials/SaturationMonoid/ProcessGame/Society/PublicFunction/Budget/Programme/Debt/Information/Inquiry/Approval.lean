import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Review

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Approval

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (views : List (View (code := model.source.code)))
  (template : Template (code := model.source.code)) (selected : Activation template)
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (actual : {view : View (code := model.source.code) // view ∈ views})
  (rival : Opponent model.source.code)

abbrev decision := Review.probe model views template selected reference actual.val actual.property rival

def cursorAt (n : Nat) : Cursor model.source.code :=
  match decision model views template selected reference actual rival with
  | .accepted rule _ _ _ => {actual.val.point.after rule rival with cut := actual.val.point.cut+n}
  | .unsupported _ _ _ | .rejected _ _ _ _ | .actualRefused _ _ _ _ _ _ _ _ _ =>
      {actual.val.point with cut := actual.val.point.cut+n}

abbrev target := (cursorAt model views template selected reference actual rival 0).source

def Protected : Prop := match decision model views template selected reference actual rival with
  | .accepted rule _ _ _ => Replanning.acceptable model (Review.domain model views) reference rule
  | .unsupported _ _ _ | .rejected _ _ _ _ | .actualRefused _ _ _ _ _ _ _ _ _ =>
      target model views template selected reference actual rival = actual.val.point.source

theorem generated_admission_protects_full_responsibility_or_keeps_the_original_source :
    Protected model views template selected reference actual rival := by
  cases result : decision model views template selected reference actual rival with
  | accepted rule work events complete => simpa only [Protected,result] using complete
  | unsupported key original outside => simp only [Protected,target,cursorAt,decision,result]
  | rejected rule work events failure => simp only [Protected,target,cursorAt,decision,result]
  | actualRefused rule work events view original opponent axis member worse =>
    simp only [Protected,target,cursorAt,decision,result]

abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨model.base,model.scope,target model views template selected reference actual rival,model.law_exact,model.task_exact⟩
abbrev facade := Native.AuthorityRuntime.facade (bound model views template selected reference actual rival)
abbrev activated (n : Nat) := Runtime.readState (bound model views template selected reference actual rival)
  (depth actual.val.point+n)
abbrev native (n : Nat) := Runtime.read (bound model views template selected reference actual rival)
  (depth actual.val.point+n)

theorem the_original_root_consumes_checked_admission_full_finance_ledger_and_next (n : Nat) :
    let current := activated model views template selected reference actual rival n
    Protected model views template selected reference actual rival ∧
      (native model views template selected reference actual rival n).joint.finance =
        Financial.accountAt (target model views template selected reference actual rival).input
          (arrival actual.val.point+n+1) ∧
      HEq ((facade model views template selected reference actual rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views template selected reference actual rival).process.stateAt
        ((facade model views template selected reference actual rival).process.successor current.state) := by
  let current := activated model views template selected reference actual rival n
  have rooted := (facade model views template selected reference actual rival).readoutAt_factorizes current .responsibilities
  refine ⟨generated_admission_protects_full_responsibility_or_keeps_the_original_source model views template selected reference actual rival,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [(native model views template selected reference actual rival n).joint_exact]
  have exactAccount := (Native.generate (target model views template selected reference actual rival)
    (depth actual.val.point+n)).finance_exact
  have address : depth actual.val.point+n+2 = arrival actual.val.point+n+1 := by
    dsimp only [depth,arrival];omega
  rw [address] at exactAccount
  exact exactAccount

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Approval
