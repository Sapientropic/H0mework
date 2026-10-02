import H0mework.Foundation.Responsibility.JointSource.Native.Compiler

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

def oldFold (current : Current registered) :
    LedgerWriteEvolutionAt N
      ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)⟩
      ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1)⟩ :=
  (FiniteGeneratedLedgerWritePatchAt.complete (oldRows program registered current)
    (oldCoverage program registered current)).toLedgerWriteEvolution

theorem patch_destination_old (current : Current registered)
    (entry : OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1))) :
    ((patch program registered current).toLedgerWriteEvolution.destination
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some current.2.state) entry)).1 =
      oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (targetCurrent program registered current).2.state)
        ((oldFold program registered current).destination entry).1 := by
  change targetRow program registered current ((oldCoverage program registered current).destinationIndex entry).castSucc =
    oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some (targetCurrent program registered current).2.state)
      ((oldRows program registered current).targetEntryAt ((oldCoverage program registered current).destinationIndex entry))
  exact Fin.lastCases_castSucc
    (motive := fun _ => OpenResponsibilityAt (World registered)
      (supportAt registered (targetCurrent program registered current)))
    (last := mathTargetEntry program registered current)
    (cast := fun index => oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some (targetCurrent program registered current).2.state)
      ((oldRows program registered current).targetEntryAt index))
    ((oldCoverage program registered current).destinationIndex entry)

theorem patch_origin_old (current : Current registered)
    (entry : OpenResponsibilityAt N
      (lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1))) :
    ((patch program registered current).toLedgerWriteEvolution.origin
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (targetCurrent program registered current).2.state) entry)).1 =
      oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some current.2.state) ((oldFold program registered current).origin entry).1 := by
  change sourceRow program registered current ((oldCoverage program registered current).originIndex entry).castSucc =
    oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some current.2.state)
      ((oldRows program registered current).sourceEntryAt ((oldCoverage program registered current).originIndex entry))
  exact Fin.lastCases_castSucc
    (motive := fun _ => OpenResponsibilityAt (World registered) (supportAt registered current))
    (last := mathSource registered current)
    (cast := fun index => oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some current.2.state) ((oldRows program registered current).sourceEntryAt index))
    ((oldCoverage program registered current).originIndex entry)

theorem patch_destination_math (current : Current registered) :
    ((patch program registered current).toLedgerWriteEvolution.destination (mathSource registered current)).1 =
      mathTargetEntry program registered current := by
  change targetRow program registered current (Fin.last _) = mathTargetEntry program registered current
  exact Fin.lastCases_last

theorem patch_origin_math (current : Current registered) :
    ((patch program registered current).toLedgerWriteEvolution.origin
      (mathTargetEntry program registered current)).1 = mathSource registered current := by
  change sourceRow program registered current (Fin.last _) = mathSource registered current
  exact Fin.lastCases_last

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
