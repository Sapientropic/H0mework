import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.World
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (base : WorldRelationNetwork)

def liftOwner (baseSupport : base.Support) (owner : OpenResponsibilityAt base baseSupport) :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (target : (process input).GeneratedState) →
    (tail : Nonempty ((process input).Run current target.current)) →
    OpenResponsibilityAt (world input base run) (support input base baseSupport run target tail)
  | _, .nil, _, _ => owner
  | _, .step prior (.admit claim), target, tail =>
      oldEntry (law := Activation.law input (generatedAccount input prior) claim)
        (state? := some (.registered target tail))
        (liftOwner baseSupport owner prior target (prependNative input (.admit claim) rfl tail))
  | _, .step prior (.cross slot obligation present boundary), target, tail =>
      liftOwner baseSupport owner prior target
        (prependNative input (.cross slot obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def transport (sourceSupport targetSupport : base.Support)
    (baseEvolution : LedgerWriteEvolutionAt base ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt base sourceSupport) :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (before : (process input).GeneratedState) →
    (prior : Nonempty ((process input).Run current before.current)) →
    (action : Action input) →
    LedgerWriteEvolutionAt (world input base run)
      ⟨support input base sourceSupport run before prior⟩
      ⟨support input base targetSupport run (action.next input before)
        (action.append_original_run input before prior)⟩
  | _, .nil, _, _, _ => baseEvolution
  | _, .step priorRun (.admit claim), before, prior, action =>
      wholeTransport
        (transport sourceSupport targetSupport baseEvolution owner priorRun before
          (prependNative input (.admit claim) rfl prior) action)
        (liftOwner input base sourceSupport owner priorRun before
          (prependNative input (.admit claim) rfl prior))
        (action.priorDebtTransport input (generatedAccount input priorRun) claim before prior)
  | _, .step priorRun (.cross slot obligation present boundary), before, prior, action =>
      transport sourceSupport targetSupport baseEvolution owner priorRun before
        (prependNative input (.cross slot obligation present boundary) rfl prior) action
  | _, .step _ (.reopen _ _ _ impossible), _, _, _ => impossible.elim

theorem transport_keeps_old_claim {sourceSupport targetSupport : base.Support}
    (baseEvolution : LedgerWriteEvolutionAt base ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt base sourceSupport)
    {current : ResponsibilityState (vocabulary input)}
    (run : (process input).Run (.empty (vocabulary input)) current)
    (before : (process input).GeneratedState)
    (prior : Nonempty ((process input).Run current before.current))
    (action : Action input)
    (entry : OpenResponsibilityAt (world input base run) (support input base sourceSupport run before prior)) :
    ((transport input base sourceSupport targetSupport baseEvolution owner run before prior action).destination
      entry).1.claim = entry.claim :=
  ((transport input base sourceSupport targetSupport baseEvolution owner run before prior action).destination
    entry).2.toDebtLineage.claim_eq.symm

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
