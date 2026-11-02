import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.ReplayRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Regression

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

abbrev seed := Reaction.Regression.source

theorem original_is_feasible : seed.code.feasible seed.reference := by decide +kernel

theorem source_laws_are_stable : Stable seed.code.law :=
  ⟨⟨by intros; rfl, by intros; rfl, by intros; rfl⟩, by intros; rfl⟩

abbrev source := replacement seed original_is_feasible
abbrev choice := selection seed original_is_feasible

theorem actual_strict_reserve_and_independent_replay :
    (source.actualExecution 0).submitted = [Reaction.Regression.need] ∧
      (source.actualExecution 0).after.stock true () = 2 ∧
      ((original seed).actualExecution 0).after.stock true () = 1 ∧
      reserve seed.code choice.policy.policy seed.reference [] seed.opponent true () = 1 ∧
      verify seed.code seed.reference choice.policy.policy = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    independent_replay_accepts_selection _ _ choice⟩


def law : RawLaw Bool Unit Unit Bool Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => true
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [((), 1)]
  mandatoryMaintenance := fun _ _ => [((), 1)]
  policy := .opaque fun current request => match request.operation with
    | .produce _ => current.technology
    | _ => true
  duration := fun _ => 1

def need : Request Bool Unit Unit Bool Unit := ⟨true, [], (), [], .use true [((), 1)] .necessity⟩
def shut : Request Bool Unit Unit Bool Unit := ⟨true, [], (), [], .revise true false⟩
def produce : Request Bool Unit Unit Bool Unit := ⟨true, [], (), [], .produce true⟩

def code : Code Bool Unit Unit Bool Unit where
  law := law
  initial := ⟨fun party _ => if party then 3 else 0, fun _ _ _ => 7, true, 0, 0⟩
  task := seed.code.task
  actions := [need, shut]
  actionLimit := 2
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => true
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0]
  eventLimit := 1
  eligible := fun events => decide (events.length = 1)
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro party; cases party <;> simp
  goods_cover := by intro good; cases good; simp
  instruments_cover := by intro instrument; cases instrument; simp

def reference : code.Policy := fun _ _ => [need]
def disabling : code.Policy := fun _ _ => [shut, need]
def opponent : Opponent code := fun _ _ _ => some ⟨.activate ⟨0, by decide +kernel⟩, by exact List.mem_cons_self⟩

theorem raw_equality_cannot_erase_an_old_legal_production :
    Reaction.NonRegression code disabling reference ∧
      ¬ NonRegression code disabling reference ∧
      Legal law (terminal code reference [] opponent) [produce] ∧
      ¬ Legal law (terminal code disabling [] opponent) [produce] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

def isBlocked {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    {code : Code Party Good Port Technology Instrument} {reference : code.Policy} : Outcome code reference → Bool
  | .selected _ => false | .blocked _ => true

theorem no_resource_returns_exact_candidate_rejections :
    isBlocked (compile Native.Regression.poorCode Native.Regression.poorPolicy Native.Regression.poor.reference_generated) = true := by
  decide +kernel


def laterIssue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 1⟩
def futureWords := [[Reaction.Regression.need], [laterIssue]]

theorem original_future_is_legal : LegalHistory seed.code.law (terminal seed.code seed.reference [] seed.opponent) futureWords := by
  decide +kernel

abbrev continuedSource := Replay.replacement seed original_is_feasible futureWords
abbrev continuedOriginal := Replay.original seed futureWords

theorem later_requests_actually_run_with_original_native_archives_and_new_issue :
    (continuedSource.actualExecution 1).submitted = [Reaction.Regression.need] ∧
      (continuedSource.actualExecution 2).submitted = [laterIssue] ∧
      (continuedSource.currentAt 4).stock true () = 1 ∧
      (continuedOriginal.currentAt 4).stock true () = 0 ∧
      Native.Regression.serviceKinds continuedSource 2 ⟨0, by decide⟩ = [true] ∧
      (Native.generate continuedSource 2).finance.current.slots.length = 1 ∧
      Institutions.Capitalism.Universal.Root.Financial.outstanding continuedSource.input
        (Native.generate continuedSource 2).finance.current = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

abbrev publicReplayFacade := ReplayRuntime.facade seed original_is_feasible source_laws_are_stable futureWords original_future_is_legal

abbrev publicOpenReactionFacade := Runtime.facade seed original_is_feasible source_laws_are_stable

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Regression
