import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Regression

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root


namespace Regression

abbrev task : PublicTaskSpec Bool Unit := ⟨[⟨false,[((),1)],.necessity⟩],0,100,by decide +kernel⟩
abbrev base := {Mandate.Source.base with mandatoryMaintenance := fun _ _ => []}
abbrev scope : Mandate.Scope (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port) :=
  ⟨task,.service,.challenge,by decide +kernel,[((),1)]⟩
abbrev law := Mandate.law base scope
abbrev initial : Mandate.Source.Current := {Mandate.Source.initial with stock := fun _ _ => 20, claims := fun _ _ _ => 0}
def proposal := Mandate.request scope initial false (.propose false)
def acceptance := Mandate.request scope (law.step initial proposal) false .accept
def serve : Mandate.Source.Action := ⟨false,[],.service,[.service],.use false [((),1)] .necessity⟩
def waste : Mandate.Source.Action := ⟨false,[],.resource,[],.use false [((),1)] .external⟩
abbrev bootstrap := [proposal, acceptance, serve]
abbrev code : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  law := law
  initial := initial
  bootstrap := bootstrap
  task := task
  actions := [waste]
  actionLimit := 1
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false,true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro p;cases p <;> simp
  goods_cover := by intro g;cases g;simp
  instruments_cover := by intro i;cases i;simp

def wastePolicy : code.Policy := fun _ _ => [waste]
theorem waste_policy_is_generated : wastePolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [wastePolicy])

abbrev source : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code
  reference := wastePolicy
  reference_generated := waste_policy_is_generated
  history := code.publicPrefix
  original := code.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original

abbrev anchor : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) := ⟨base,scope,source,rfl,rfl⟩

abbrev reference : Program anchor 1 := ⟨[some wastePolicy],by
  apply List.mem_filter.mpr
  exact ⟨(mem_sequences_iff _ _ _).mpr ⟨by decide +kernel,by
    intro control member
    have same := List.mem_singleton.mp member
    subst control
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨wastePolicy,waste_policy_is_generated,rfl⟩)⟩,rfl⟩⟩

abbrev efficient : Program anchor 1 := ⟨[none],by
  apply List.mem_filter.mpr
  exact ⟨(mem_sequences_iff _ _ _).mpr ⟨by decide +kernel,by simp [menu]⟩,rfl⟩⟩

abbrev origin : Origin anchor where
  history := ⟨source.history,source.original⟩
  response := ⟨Reaction.restrict code source.opponent,Reaction.restriction_is_generated code source.opponent⟩
  side := .original

abbrev rival : Opponent code := fun _ _ _ => some ⟨.activate 0,by simp [code]⟩
abbrev world : World anchor 1 := realizedWorld anchor 1 origin reference rival 0
abbrev laterWorld : World anchor 1 := {world with phase := 1}
abbrev publicInformationFacade := Runtime.facade anchor 1 world 0 reference

/-- The two stations retain separate paid records; a sender's private read is not a broadcast. -/
def knowledgeProgramme (_site : Fin Recall.Regression.base.sites) (history : List (Notice Recall.Regression.base)) :=
  if LocalNotice.sent 1 1 ∈ history then [Recall.Regression.repay,Recall.Regression.serve] else [Recall.Regression.serve]

def knowledgePolicy : Recall.Regression.code.Policy := tabulate Recall.Regression.base 3 knowledgeProgramme

theorem knowledge_policy_is_generated : knowledgePolicy ∈ Recall.Regression.code.policies := by
  apply every_supported_history_programme_is_actually_tabulated
  intro site history _
  simp only [knowledgeProgramme]
  split <;> exact (mem_words_iff _ _ _).mpr (by simp)

abbrev learningCode := {Recall.Regression.code with
  eventAlphabet := [.send 0 1,.deliver 0,.deliver 1,.activate 0,.activate 1]}

def learningOpponent : Opponent learningCode := fun _ past _ => match past.length with
  | 0 => some ⟨.send 0 1,by simp [learningCode]⟩
  | 1 => some ⟨.deliver 0,by simp [learningCode]⟩
  | _ => none
abbrev learningInput : Input learningCode := ⟨learningOpponent,5⟩

abbrev learningSource (financed : Bool) : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := learningCode
  reference := Recall.Regression.policy
  reference_generated := Recall.Regression.policy_is_generated
  history := (Recall.Regression.source financed).history
  original := (Recall.Regression.source financed).original
  opponent := fun _ _ _ => none
  side := .original
  feedback? := some learningInput

abbrev learningAnchor (financed : Bool) : Native.Authority.Bound (Party := Bool) (Good := Unit)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) :=
  {Recall.Regression.bound financed with source := learningSource financed}

abbrev knowledgeRule : Synthesis.Rule (learningAnchor true) :=
  ⟨some knowledgePolicy,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨knowledgePolicy,knowledge_policy_is_generated,rfl⟩)⟩

def atWorker (worker : Fin 2) : Opponent learningCode := fun _ _ _ =>
  some ⟨.activate worker,by
    have bound := worker.isLt
    have numeric : worker.val = 0 ∨ worker.val = 1 := by omega
    have alternatives : worker = 0 ∨ worker = 1 := numeric.imp (fun same => Fin.ext same) (fun same => Fin.ext same)
    rcases alternatives with rfl | rfl <;> simp [learningCode]⟩

abbrev learnedBranch (financed : Bool) (worker : Fin 2) :=
  Future.target (learningSource financed) learningInput 1 (atWorker worker) [some knowledgePolicy]

theorem actual_paid_private_read_changes_only_its_own_workers_choice :
    ((learningSource true).feedbackState learningInput 1).frame.inbox 0 ≠
        ((learningSource false).feedbackState learningInput 1).frame.inbox 0 ∧
      ((learningSource true).feedbackState learningInput 1).frame.inbox 1 =
        ((learningSource false).feedbackState learningInput 1).frame.inbox 1 ∧
      ((learnedBranch true 0).actualExecution 3).submitted = [Recall.Regression.repay,Recall.Regression.serve] ∧
      ((learnedBranch false 0).actualExecution 3).submitted = [Recall.Regression.serve] ∧
      ((learnedBranch true 1).actualExecution 3).submitted = [Recall.Regression.serve] ∧
      ((learnedBranch false 1).actualExecution 3).submitted = [Recall.Regression.serve] := by
  decide +kernel


end Regression


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information
