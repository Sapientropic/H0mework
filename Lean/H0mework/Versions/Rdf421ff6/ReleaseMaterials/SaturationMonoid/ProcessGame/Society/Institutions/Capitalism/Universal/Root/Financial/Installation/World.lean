import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Activation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.JointTransport

/-! Root worlds are folded from the original native lifecycle run.  Each
admission extends the existing world once; a carry changes no claim type.
Every old debt support reads the same whole generated account. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (base : WorldRelationNetwork)

def generatedAccount {current : ResponsibilityState (vocabulary input)}
    (run : (process input).Run (.empty (vocabulary input)) current) : (process input).GeneratedState :=
  ⟨current, run⟩

def world : {current : ResponsibilityState (vocabulary input)} →
    (process input).Run (.empty (vocabulary input)) current → WorldRelationNetwork
  | _, .nil => base
  | _, .step prior (.admit claim) =>
      ExtendedNetwork (world prior) (Activation.law input (generatedAccount input prior) claim)
  | _, .step prior (.cross _ _ _ _) => world prior
  | _, .step _ (.reopen _ _ _ impossible) => impossible.elim

theorem prependNative {first middle last : ResponsibilityState (vocabulary input)}
    (edge : (process input).Edge first)
    (same : edge.target = middle)
    (tail : Nonempty ((process input).Run middle last)) : Nonempty ((process input).Run first last) := by
  subst middle
  exact tail.map (fun run => (NativeResponsibilityProcess.Run.step .nil edge).concatRuns (process input) run)

def support (baseSupport : base.Support) :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (target : (process input).GeneratedState) →
    Nonempty ((process input).Run current target.current) → (world input base run).Support
  | _, .nil, _, _ => baseSupport
  | _, .step prior (.admit claim), target, tail =>
      (support baseSupport prior target (prependNative input (.admit claim) rfl tail),
        some (.registered target tail))
  | _, .step prior (.cross slot obligation present boundary), target, tail =>
      support baseSupport prior target (prependNative input (.cross slot obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def currentSupport (baseSupport : base.Support) (state : (process input).GeneratedState) :
    (world input base state.generated).Support :=
  support input base baseSupport state.generated state ⟨.nil⟩

theorem admission_world_is_exact_extension (state : (process input).GeneratedState) (claim : IssuedClaim input) :
    world input base (admit input state claim).generated =
      ExtendedNetwork (world input base state.generated) (Activation.law input state claim) := rfl

theorem admission_support_shares_whole_account (baseSupport : base.Support)
    (state : (process input).GeneratedState) (claim : IssuedClaim input) :
    currentSupport input base baseSupport (admit input state claim) =
      (support input base baseSupport state.generated (admit input state claim)
        ⟨.step .nil (.admit (P := process input) claim)⟩, some (Activation.first input state claim)) := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
