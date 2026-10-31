import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.JointTransport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (base : WorldRelationNetwork) (initial : (process input depth count).GeneratedState)

def owner (baseSupport : base.Support) (baseOwner : OpenResponsibilityAt base baseSupport) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (target : (process input depth count).GeneratedState) →
    (tail : Nonempty ((process input depth count).Run current target.current)) →
    OpenResponsibilityAt (world input depth count base initial run)
      (support input depth count base initial baseSupport run target tail)
  | _, .nil, _, _ => baseOwner
  | _, .step prior (.admit claim), target, tail =>
      oldEntry (owner baseSupport baseOwner prior target (prependEdge input depth count (.admit claim) rfl tail))
  | _, .step prior (.cross slot obligation present boundary), target, tail =>
      owner baseSupport baseOwner prior target (prependEdge input depth count (.cross slot obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def itemEvolution {sourceSupport targetSupport : base.Support}
    (baseEvolution : LedgerWriteEvolutionAt base ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (baseOwner : OpenResponsibilityAt base sourceSupport) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (before : (process input depth count).GeneratedState) →
    (tail : Nonempty ((process input depth count).Run current before.current)) →
    (item : ActualItem input depth count) →
    LedgerWriteEvolutionAt (world input depth count base initial run)
      ⟨support input depth count base initial sourceSupport run before tail⟩
      ⟨support input depth count base initial targetSupport run ((consume input depth count item before).next input depth count)
        (tail.map fun prior => prior.concatRuns (process input depth count) ((consume input depth count item before).transition input depth count))⟩
  | _, .nil, _, _, _ => baseEvolution
  | _, .step prior (.admit claim), before, tail, item =>
      Financial.Installation.wholeTransport
        (itemEvolution baseEvolution baseOwner prior before (prependEdge input depth count (.admit claim) rfl tail) item)
        (owner input depth count base initial sourceSupport baseOwner prior before (prependEdge input depth count (.admit claim) rfl tail))
        (Activation.SameDebtTransport.actualInstruction (input := input) (depth := depth) (count := count)
          (before := generatedAccount input depth count initial prior) (claim := claim) before tail item)
  | _, .step prior (.cross slot obligation present boundary), before, tail, item =>
      itemEvolution baseEvolution baseOwner prior before
        (prependEdge input depth count (.cross slot obligation present boundary) rfl tail) item
  | _, .step _ (.reopen _ _ _ impossible), _, _, _ => impossible.elim

#print axioms itemEvolution

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future
