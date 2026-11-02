import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Deployment
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Regression
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

def meter : Budget.Programme.Flow.Regression.Action :=
  {Budget.Programme.Flow.Regression.waste with operation := .use false [(false,1/1000),(true,1/1000)] .external}
def ruin : Budget.Programme.Flow.Regression.Action :=
  {Budget.Programme.Flow.Regression.waste with operation := .use false [(false,100)] .external}
def doubleFee : Budget.Programme.Flow.Regression.Action :=
  {meter with operation := .use false [(false,2/1000),(true,2/1000)] .external}
abbrev code := {Budget.Programme.Flow.Regression.code with actions := [meter,doubleFee,ruin]}
def idle : code.Policy := fun _ _ => []
theorem idle_generated : idle ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [idle])
abbrev rival : Opponent code := fun _ _ _ => none
def point (budget : Nat) : Cursor code :=
  ⟨idle,idle_generated,code.publicPrefix,code.public_prefix_is_an_actual_generated_history,
    rival,.original,⟨rival,budget⟩,[],0,code.publicPrefix.length+1⟩
def view (budget : Nat) : View (code := code) := ⟨point budget,⟨arrival (point budget),by omega⟩⟩
abbrev model : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := Budget.Programme.Flow.Regression.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨Budget.Programme.Flow.Regression.base,Budget.Programme.Flow.Regression.scope,(point 1).source,rfl,rfl⟩
abbrev domain := [point 1]
abbrev original := Replay.protocol (code := code) 0 [doubleFee] (by apply (mem_words_iff _ _ _).mpr;simp)
abbrev reference : Program code (horizon domain) := ⟨[original],by decide +kernel⟩
def quote : Charge.Quote (Party := Bool) (Good := Bool) (Port := Budget.Programme.Flow.Regression.Port)
    (Technology := Unit) (Instrument := Unit) := ⟨[],[meter]⟩
abbrev paid := Charge.trace quote (code := code) 0 (view 1) rival
abbrev endAt := Charge.endAt quote model 0 (view 1) rival
abbrev answer := Runtime.read model domain original reference 0 quote (view 1) rival endAt
abbrev publicPaidSearchFacade := Runtime.facade model domain original reference 0 quote (view 1) rival
abbrev publicZeroBudgetSearchFacade := Runtime.facade model domain original reference 0 quote (view 0) rival
abbrev waitRule := Replay.protocol (code := code) 0 [] (by apply (mem_words_iff _ _ _).mpr;simp)
abbrev waitingPoint := Evidence.after (view 3) waitRule rival
abbrev publicWaitingSearchFacade := Runtime.facade model domain original reference 0 quote waitingPoint rival
abbrev blockedReference : Program code (horizon domain) := ⟨[waitRule],by decide +kernel⟩
abbrev blockedAnswer := Runtime.read model domain original blockedReference 0 quote (view 1) rival endAt
abbrev publicRejectedSearchFacade := Runtime.facade model domain original blockedReference 0 quote (view 1) rival

def unsupportedQuote := {quote with selection := [Budget.Programme.Flow.Regression.waste]}
def refusedQuote := {quote with selection := [ruin]}
def installed : Cursor code := Deployment.install model domain original reference 0 quote (view 1) rival endAt
def installedBound : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := Budget.Programme.Flow.Regression.Port)
    (Technology := Unit) (Instrument := Unit) := Deployment.bound model domain original reference 0 quote (view 1) rival endAt
abbrev publicInstalledPaidSearchFacade := Native.AuthorityRuntime.facade installedBound

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Regression
