import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRequestAuthentication
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationSource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information Agency.Protocol Continuation

abbrev query (mode : RequestResponseSource.Mode) :=
  LocalRequestAuthentication.generate RequestResponseSource.vocabulary (RequestResponseSource.law mode)
    (RequestResponseSource.start mode) ((RequestResponseSource.stages mode).map Prod.fst) 1
    ((EventStep.seed (RequestResponseSource.beforeResponse mode)).frame.inbox 1)

abbrev rule (mode : RequestResponseSource.Mode) :=
  LocalRequestAuthentication.protocol RequestResponseSource.vocabulary (RequestResponseSource.law mode)
    (RequestResponseSource.start mode) ((RequestResponseSource.stages mode).map Prod.fst)

abbrev row (mode : RequestResponseSource.Mode) := StageTrace.material
  (RequestResponseSource.beforeResponse mode) (rule mode) (RequestResponseSource.environment mode)

abbrev full (mode : RequestResponseSource.Mode) :=
  LocalRequestAuthentication.produce RequestResponseSource.vocabulary (RequestResponseSource.law mode)
    (RequestResponseSource.start mode) (RequestResponseSource.stages mode) (RequestResponseSource.environment mode)

abbrev final (mode : RequestResponseSource.Mode) := EventHistory.execute (RequestResponseSource.start mode) (full mode)

abbrev noOrigin := (RequestResponseSource.quiet .normal, RequestResponseSource.environment .normal) ::
  (RequestResponseSource.stages .normal).tail

def wrongVote : Rule (RequestResponseSource.code .normal) where
  work := ⟨fun key _ => if key.1 = 0 then [RequestResponseSource.positive] else [], by
    apply (RequestResponseSource.code .normal).every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    split
    · simp
    · simp⟩
  events := (RequestResponseSource.vote .normal).events

abbrev wrongSigner := (wrongVote, RequestResponseSource.environment .normal) :: (RequestResponseSource.stages .normal).tail

abbrev expiring : StageReception.Law (RequestResponseSource.code .normal) :=
  ⟨(fun _ current => if current.round ≤ (RequestResponseSource.code .normal).initial.round +
      (RequestResponseSource.source .normal).history.length + 8 then RequestResponseSource.slot
    else {RequestResponseSource.slot with epoch := 1}), 1⟩

abbrev stale := RequestResponseSource.stages .normal ++
  [(RequestResponseSource.quiet .normal, RequestResponseSource.environment .normal)]

def atPast (past : List (EventHistory.Stage (code := RequestResponseSource.code .normal))) :=
  LocalRequestAuthentication.generate RequestResponseSource.vocabulary (RequestResponseSource.law .normal)
    (RequestResponseSource.start .normal) (past.map Prod.fst) 1
    ((EventStep.seed (EventHistory.execute (RequestResponseSource.start .normal) past)).frame.inbox 1)

namespace Ambiguity

def drain : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 7)] .external⟩
abbrev code : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {RequestResponseSource.code .normal with
    sendCost := fun _ _ => []
    eventAlphabet := [.activate 0, .activate 1, .send 0 1, .deliver 0, .adversary drain]
    eligible := fun _ => true}
abbrev source : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code
  reference := fun _ _ => []
  reference_generated := by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := code.publicPrefix
  original := code.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev model : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨Distributed.Recall.Information.Regression.base, Distributed.Recall.Information.Regression.scope, source, rfl, rfl⟩
abbrev origin : Origin model where
  history := ⟨source.history, source.original⟩
  response := ⟨Reaction.restrict code source.opponent, Reaction.restriction_is_generated _ _⟩
  side := .original
abbrev start := EventHistory.ofOrigin model 12 origin
abbrev environment : Opponent code := fun _ _ _ => none
abbrev quiet : Rule code := SilentWindow.quiet
abbrev draining : Opponent code := fun _ _ _ => some ⟨.adversary drain, by simp [code]⟩
abbrev delivery : Opponent code := fun _ _ _ => some ⟨.deliver 0, by simp [code]⟩
def vote : Rule code where
  work := ⟨fun key _ => if key.1 = 0 then [RequestResponseSource.yes] else [], by
    apply code.every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    split <;> simp⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.activate 0, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove code 0)
    else ⟨none, List.mem_cons_self⟩
def send : Rule code where
  work := ⟨fun _ _ => [], by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if same : key.1 = 0 then same.symm ▸
    (⟨some ⟨.send 0 1, by simp [code]⟩, by simp [ownMoves, code]⟩ : LocalMove code 0)
    else ⟨none, List.mem_cons_self⟩
def past (resourceDeviation : Bool) : List (EventHistory.Stage (code := code)) :=
  [(quiet, environment), (quiet, if resourceDeviation then draining else environment), (quiet, environment),
    (quiet, environment), (vote, environment), (quiet, environment), (quiet, environment),
    (quiet, environment), (send, environment), (quiet, delivery)]
abbrev current (resourceDeviation : Bool) := EventHistory.execute start (past resourceDeviation)
abbrev vocabulary := RequestResponseSource.vocabulary
abbrev law : StageReception.Law code := ⟨fun _ _ => RequestResponseSource.slot, 1⟩
abbrev statement : RequestAttestation.Statement (code := code) :=
  ⟨⟨4, 0, 0, false, RequestResponseSource.slot, true, 1⟩, RequestResponseSource.yes⟩
abbrev query (resourceDeviation : Bool) := LocalRequestAuthentication.generate vocabulary law start
  ((past resourceDeviation).map Prod.fst) 1 ((EventStep.seed (current resourceDeviation)).frame.inbox 1)

end Ambiguity

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationSource
