import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation

/-! Extend the installed old world along the actual unified native suffix.
Only admissions in this suffix create rows; the initial old account is not
re-admitted. Every new row reads the same generated whole account. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (base : WorldRelationNetwork) (initial : (process input depth count).GeneratedState)

def generatedAccount {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run initial.current current) : (process input depth count).GeneratedState :=
  ⟨current, initial.generated.concatRuns (process input depth count) run⟩

def world : {current : ResponsibilityState (vocabulary input depth count)} →
    (process input depth count).Run initial.current current → WorldRelationNetwork
  | _, .nil => base
  | _, .step prior (.admit claim) =>
      ExtendedNetwork (world prior) (Activation.law input depth count (generatedAccount input depth count initial prior) claim)
  | _, .step prior (.cross _ _ _ _) => world prior
  | _, .step _ (.reopen _ _ _ impossible) => impossible.elim

theorem prependEdge {first middle last : ResponsibilityState (vocabulary input depth count)}
    (edge : (process input depth count).Edge first) (same : edge.target = middle)
    (tail : Nonempty ((process input depth count).Run middle last)) :
    Nonempty ((process input depth count).Run first last) := by
  subst middle
  exact tail.map fun run => (NativeResponsibilityProcess.Run.step .nil edge).concatRuns (process input depth count) run

def support (baseSupport : base.Support) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (target : (process input depth count).GeneratedState) →
    Nonempty ((process input depth count).Run current target.current) →
    (world input depth count base initial run).Support
  | _, .nil, _, _ => baseSupport
  | _, .step prior (.admit claim), target, tail =>
      (support baseSupport prior target (prependEdge input depth count (.admit claim) rfl tail),
        some (.registered target tail))
  | _, .step prior (.cross slot obligation present boundary), target, tail =>
      support baseSupport prior target (prependEdge input depth count (.cross slot obligation present boundary) rfl tail)
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

def AllNewRowsRead (target : (process input depth count).GeneratedState) :
    {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (world input depth count base initial run).Support → Prop
  | _, .nil, _ => True
  | _, .step prior (.admit _), state => AllNewRowsRead target prior state.1 ∧
      match state.2 with
      | some (.registered account _) => account = target
      | _ => False
  | _, .step prior (.cross _ _ _ _), state => AllNewRowsRead target prior state
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

def originalRestriction : {current : ResponsibilityState (vocabulary input depth count)} →
    (run : (process input depth count).Run initial.current current) →
    (world input depth count base initial run).Support → base.Support
  | _, .nil, value => value
  | _, .step prior (.admit _), value => originalRestriction prior value.1
  | _, .step prior (.cross _ _ _ _), value => originalRestriction prior value
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

theorem original_restriction_is_the_same_installed_support (baseSupport : base.Support)
    {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run initial.current current)
    (target : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run current target.current)) :
    originalRestriction input depth count base initial run
      (support input depth count base initial baseSupport run target tail) = baseSupport := by
  induction run with
  | nil => rfl
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact inherited (prependEdge input depth count (.admit claim) rfl tail)
      | cross slot obligation present boundary =>
          exact inherited (prependEdge input depth count (.cross slot obligation present boundary) rfl tail)
      | reopen _ _ _ impossible => exact impossible.elim

theorem all_new_rows_read_the_same_computed_account (baseSupport : base.Support)
    {current : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run initial.current current)
    (target : (process input depth count).GeneratedState)
    (tail : Nonempty ((process input depth count).Run current target.current)) :
    AllNewRowsRead input depth count base initial target run
      (support input depth count base initial baseSupport run target tail) := by
  induction run with
  | nil => trivial
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact ⟨inherited (prependEdge input depth count (.admit claim) rfl tail), rfl⟩
      | cross slot obligation present boundary =>
          exact inherited (prependEdge input depth count (.cross slot obligation present boundary) rfl tail)
      | reopen _ _ _ impossible => exact impossible.elim

#print axioms world
#print axioms all_new_rows_read_the_same_computed_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future
