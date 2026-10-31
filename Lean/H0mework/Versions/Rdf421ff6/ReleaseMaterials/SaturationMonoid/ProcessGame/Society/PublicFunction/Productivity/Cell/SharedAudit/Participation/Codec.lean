import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program

inductive Command where
  | accept | challenge | exit | refuse
  deriving DecidableEq

def Command.cost : Command → ℚ
  | .challenge => 2
  | _ => 1

def Command.gates : Command → List Port
  | .accept => [.revision]
  | .challenge => [.revision, .revision]
  | .exit => [.revision, .revision, .revision]
  | .refuse => [.revision, .revision, .revision, .revision]

def request (actor : Party) (command : Command) : RequestAt :=
  ⟨actor, [], .revision, command.gates, .use actor [(.labor, command.cost)] .contribution⟩

def readGates : List Port → Option Command
  | [.revision] => some .accept
  | [.revision, .revision] => some .challenge
  | [.revision, .revision, .revision] => some .exit
  | [.revision, .revision, .revision, .revision] => some .refuse
  | _ => none

def decode (attempt : RequestAt) : Option (Party × Command) :=
  match attempt.operation with
  | .use actor goods .contribution =>
    match readGates attempt.gates with
    | some command =>
      if attempt.signer = actor ∧ attempt.consents = [] ∧ attempt.purpose = .revision ∧
          goods = [(.labor, command.cost)] then some (actor, command) else none
    | none => none
  | _ => none

theorem encode_decode (actor : Party) (command : Command) :
    decode (request actor command) = some (actor, command) := by
  cases command <;> simp [decode, request, readGates, Command.gates, Command.cost]

theorem decoded_request_is_self_signed (attempt : RequestAt) (actor : Party) (command : Command)
    (decoded : decode attempt = some (actor, command)) : attempt.signer = actor := by
  unfold decode at decoded
  split at decoded
  · split at decoded
    · split at decoded
      next checked => cases decoded; exact checked.1
      next => cases decoded
    · cases decoded
  · cases decoded

inductive Standing where
  | available | active | released | declined
  deriving DecidableEq

def CanRun (standing : Standing) : Command → Prop
  | .accept => standing ≠ .active
  | .refuse => standing = .available
  | .challenge | .exit => standing = .active

instance (standing : Standing) (command : Command) : Decidable (CanRun standing command) := by
  cases command <;> unfold CanRun <;> infer_instance

def advance : Standing → Command → Standing
  | _, .accept => .active
  | standing, .challenge => standing
  | _, .exit => .released
  | _, .refuse => .declined

abbrev Register := Party → Standing

def update (register : Register) (item : Born.Item) : Register :=
  match decode item.request with
  | none => register
  | some (actor, command) =>
    if actor ∈ ([1, 2] : List Party) ∧ CanRun (register actor) command ∧ law.Valid item.before item.request then
      fun party => if party = actor then advance (register actor) command else register party
    else register

theorem another_signer_cannot_change_your_standing (register : Register) (item : Born.Item)
    (actor : Party) (other : item.request.signer ≠ actor) : update register item actor = register actor := by
  cases decoded : decode item.request with
  | none => simp [update, decoded]
  | some pair =>
    rcases pair with ⟨sender, command⟩
    have owns := decoded_request_is_self_signed _ _ _ decoded
    have different : actor ≠ sender := by
      intro same
      exact other (owns.trans same.symm)
    simp only [update, decoded]
    split_ifs <;> simp_all

def initialRegister : Register := fun _ => .available

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
