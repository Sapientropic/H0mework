import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Mandate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cuts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Authority

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

abbrev Sources (base : RawLaw Party Good Port Technology Instrument)
    (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)) :=
  {source : Machine Party Good Port (Mandate.State Party Technology) Instrument //
    source.code.law = Mandate.law base scope ∧ source.code.task = scope.task}

def sourceIndex : Sources bound.base bound.scope :=
  ⟨bound.source, bound.law_exact, bound.task_exact⟩

/-- A common law and task share one native vocabulary; each index still reads its own actual input. -/
def programme : Mandate.Challenge.ProgrammeFamily bound.base bound.scope (Sources bound.base bound.scope) where
  inputAt := fun source => source.val.input
  law_exact := fun source => source.property.1

theorem challenge_reads_the_exact_emitting_input :
    Mandate.Challenge.I (programme bound) (sourceIndex bound) = bound.source.input := rfl

abbrev Challenge := Mandate.Challenge.Claim (programme bound) (sourceIndex bound)
abbrev ChallengeHistory (claim : Challenge bound) := Mandate.Challenge.History (programme bound) (sourceIndex bound) claim
abbrev challengesAt (count : Nat) := Mandate.Challenge.recordsAt (programme bound) (sourceIndex bound) count

structure FullDisposition (depth : Nat) where
  authority : Disposition bound depth
  authority_exact : authority = generate bound depth
  challenges : List (Sigma fun claim : Challenge bound => ChallengeHistory bound claim)
  challenges_exact : challenges = challengesAt bound (depth + 2)

def fullGenerate (depth : Nat) : FullDisposition bound depth :=
  ⟨generate bound depth, rfl, challengesAt bound (depth + 2), rfl⟩

theorem every_actual_signed_challenge_is_natively_admitted
    (position : Mandate.Challenge.Position (programme bound) (sourceIndex bound)) (claim : Challenge bound)
    (decoded : Mandate.Challenge.read (programme bound) (sourceIndex bound) position = some claim)
    (depth : Nat) (inside : position.ordinal < depth + 2) :
    (⟨claim, Mandate.Challenge.through (programme bound) (sourceIndex bound) claim (depth + 2)⟩ :
      Sigma fun claim : Challenge bound => ChallengeHistory bound claim) ∈ (fullGenerate bound depth).challenges :=
  Mandate.Challenge.every_decoded_claim_is_consumed (programme bound) (sourceIndex bound) position claim decoded _ inside

def challengeContinuation (claim : Challenge bound) (count later : Nat) :
    (Mandate.Challenge.process (programme bound) (sourceIndex bound) claim).Run
      (Mandate.Challenge.through (programme bound) (sourceIndex bound) claim count).state.current
      (Mandate.Challenge.through (programme bound) (sourceIndex bound) claim (count + later)).state.current :=
  Mandate.Challenge.fromActualCut (programme bound) (sourceIndex bound) claim count later

theorem challenge_retains_its_original_admission_and_bearer (claim : Challenge bound)
    (target : Mandate.Challenge.Target (programme bound) (sourceIndex bound) claim) :
    (Mandate.Challenge.tracked (programme bound) (sourceIndex bound) claim target).admission =
        (Mandate.Challenge.obligation (programme bound) (sourceIndex bound) claim).admission ∧
      (Mandate.Challenge.tracked (programme bound) (sourceIndex bound) claim target).bearer = claim.actor (programme bound) (sourceIndex bound) ∧
      (Mandate.Challenge.tracked (programme bound) (sourceIndex bound) claim target).content = claim ∧
      (Mandate.Challenge.tracked (programme bound) (sourceIndex bound) claim target).scope = claim.origin (programme bound) (sourceIndex bound) ∧
      (Mandate.Challenge.tracked (programme bound) (sourceIndex bound) claim target).lineage = claim.origin (programme bound) (sourceIndex bound) :=
  Mandate.Challenge.original_admission_and_responsibility_are_retained (programme bound) (sourceIndex bound) claim target

theorem every_challenge_history_is_its_own_actual_native_run (claim : Challenge bound) (count : Nat) :
    (Mandate.Challenge.through (programme bound) (sourceIndex bound) claim count).state.current.history =
      (Mandate.Challenge.through (programme bound) (sourceIndex bound) claim count).state.generated.events :=
  Mandate.Challenge.actual_native_history (programme bound) (sourceIndex bound) claim count

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Authority
