import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Tariff
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)

/-- An empty input carrier receives its own source word before entering the
existing feedback cursor. Existing inventories are not submitted again. -/
def prepared : Inventory epoch :=
  if inventory.inputs = [] then World.submit inventory (Input.Event.Future.ownWord inventory) else inventory

def preparation : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) ⟨epoch,prepared inventory⟩ := by
  unfold prepared
  split
  · exact .submit inventory (Input.Event.Future.ownWord inventory)
  · exact .same _

theorem prepared_has_an_actual_input : (prepared inventory).inputs ≠ [] := by
  unfold prepared
  split
  next empty =>
    simp only [World.submit,empty,List.nil_append]
    intro absent;cases absent
  next nonempty => exact nonempty

def received := (prepared inventory).inputs
def firstWord := (received inventory).headD []
def laterWords := (received inventory).drop 1

theorem received_exact : firstWord inventory :: laterWords inventory = received inventory := by
  have nonempty := prepared_has_an_actual_input inventory
  unfold firstWord laterWords received
  cases actual : (prepared inventory).inputs with
  | nil => exact False.elim (nonempty actual)
  | cons head tail => rfl

def ports : List Input.Intent := [.admission,.challenge,.exit,.renewal,.revision]

theorem every_port_is_included (intent : Input.Intent) : intent ∈ ports := by
  cases intent <;> simp [ports]
def futureWords := ports.map fun intent => pending ++ Input.emit (prepared inventory) intent
def rates := Input.Recovery.Tariff.actions epoch (prepared inventory).inputs

/-- Actual history remains ordered. The future alphabet includes all five
native emissions, the raw residual, the source word and every offered fee. -/
def language : List (List Action) :=
  received inventory ++ [pending,Input.Event.Future.ownWord (prepared inventory)] ++
    futureWords inventory pending ++ (rates inventory).map (fun request => [request])

private theorem length_in_language (words : List (List Action)) (word : List Action) (member : word ∈ words) :
    word.length ≤ (words.map List.length).sum := by
  induction words with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.map_cons,List.sum_cons]
      rcases List.mem_cons.mp member with same | later
      · subst word;omega
      · have smaller := ih later;omega

def code : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  let future := futureWords inventory pending
  let lexicon := received inventory ++ [pending,Input.Event.Future.ownWord (prepared inventory)] ++
    future ++ (rates inventory).map (fun request => [request])
  let alphabet := lexicon.flatten
  {
  law := Mandate.law base epoch.scope
  initial := epoch.source.seed.initial
  bootstrap := epoch.source.seed.original
  task := epoch.scope.task
  actions := alphabet
  actionLimit := (lexicon.map List.length).sum
  sites := 2
  signals := 1
  initialSignal := 0
  siteParty := fun site => site.val = 1
  readLocal := fun _ _ => 0
  historyAlphabet := future
  historyLimit := Input.Event.Future.Expiry.horizon epoch.bound
  eventAlphabet := [.activate 0,.activate 1] ++
    alphabet.map Event.adversary
  eventLimit := 1
  eligible := fun _ => true
  parties := [false,true]
  goods := [.feedstock,.service]
  instruments := [()]
  parties_cover := by intro actor;cases actor <;> simp
  goods_cover := by intro good;cases good <;> simp
  instruments_cover := by intro instrument;cases instrument;simp }

theorem every_language_word_is_a_native_policy_word (word : List Action)
    (member : word ∈ language inventory pending) :
    word ∈ words (code inventory pending).actions (code inventory pending).actionLimit := by
  apply (mem_words_iff _ _ _).mpr
  refine ⟨length_in_language _ word member,?_⟩
  intro request inside
  exact List.mem_flatten.mpr ⟨word,member,inside⟩

theorem every_own_scope_port_is_supported (intent : Input.Intent) :
    pending ++ Input.emit (prepared inventory) intent ∈
      words (code inventory pending).actions (code inventory pending).actionLimit := by
  apply every_language_word_is_a_native_policy_word
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨intent,
    every_port_is_included intent,rfl⟩

theorem every_actual_rate_is_supported (request : Action) (offered : request ∈ rates inventory) :
    [request] ∈ words (code inventory pending).actions (code inventory pending).actionLimit := by
  apply every_language_word_is_a_native_policy_word
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨request,offered,rfl⟩

def constant (word : List Action) : (code inventory pending).Policy := fun _ _ => word

theorem constant_is_generated (word : List Action) (member : word ∈ language inventory pending) :
    constant inventory pending word ∈ (code inventory pending).policies :=
  Code.every_local_policy_is_enumerated _ _ (fun _ _ => every_language_word_is_a_native_policy_word inventory pending word member)

theorem first_word_is_in_the_language : firstWord inventory ∈ language inventory pending := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  rw [←received_exact inventory]
  exact List.mem_cons_self

def initialOpponent : Opponent (code inventory pending) := fun _ past _ =>
  if past = [] then some ⟨.activate ⟨0,by change 0 < 2;decide⟩,by exact List.mem_cons_self⟩ else none

def continuingOpponent : Opponent (code inventory pending) := fun _ _ _ =>
  some ⟨.activate ⟨0,by change 0 < 2;decide⟩,by exact List.mem_cons_self⟩

abbrev baseMachine : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code inventory pending
  reference := constant inventory pending (firstWord inventory)
  reference_generated := constant_is_generated inventory pending _ (first_word_is_in_the_language inventory pending)
  history := (code inventory pending).publicPrefix
  original := Code.public_prefix_is_an_actual_generated_history _
  opponent := initialOpponent inventory pending
  side := .original
  feedback? := some ⟨continuingOpponent inventory pending,
    (laterWords inventory).length + Input.Event.Future.Expiry.horizon epoch.bound⟩

def schedule : List (Option (code inventory pending).Policy) :=
  (laterWords inventory).map fun word => some (constant inventory pending word)

abbrev machine := Feedback.Execution.target (baseMachine inventory pending) 0 (schedule inventory pending)

def cursor : Continuation.Cursor (code inventory pending) :=
  let source := machine inventory pending
  ⟨source.reference,source.reference_generated,source.history,source.original,source.opponent,source.side,
    ⟨continuingOpponent inventory pending,
      (laterWords inventory).length + Input.Event.Future.Expiry.horizon epoch.bound⟩,
    source.feedbackOverrides,(laterWords inventory).length,(received inventory).length+1⟩

theorem cursor_uses_the_same_generated_machine : (cursor inventory pending).source = machine inventory pending := rfl

def nativeSource : Native.Authority.Sources base epoch.scope :=
  ⟨(cursor inventory pending).source,rfl,rfl⟩

def model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨base,epoch.scope,(nativeSource inventory pending).val,rfl,rfl⟩
def worldInput : Computation.Search.Segmented.Publication.Learning.Paid.Owned.WorldInput base epoch.scope :=
  .actual (prepared inventory)

theorem the_compiled_law_and_task_are_the_actual_scope :
    (model inventory pending).source.code.law = Mandate.law base epoch.scope ∧
    (model inventory pending).source.code.task = epoch.source.seed.task := ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
