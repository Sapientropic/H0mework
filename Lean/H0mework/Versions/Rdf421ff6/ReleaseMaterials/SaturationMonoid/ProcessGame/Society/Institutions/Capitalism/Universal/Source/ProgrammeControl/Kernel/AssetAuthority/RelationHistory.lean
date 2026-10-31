import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth

/-! Relation lookup folds the existing root history, exactly as actor birth
lookup does.  The value retained is an original GeneratedRelation, including
its actual source occurrence.  No relation registry or new identity is made. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RelationHistory

open ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Visit := ActualBirth.Visit input
abbrev root := ActualBirth.root input

def origin (visit : Visit input) := (Registered.reader input).raw (ActualBirth.occurrence input visit)

def presentAt (visit : Visit input) (port : Port) : Prop :=
  ∃ incidence ∈ relationIncidences input.law (origin input visit), incidence.1 = port

structure Witness (port : Port) where
  private mk ::
  visit : Visit input
  incidence : Port × Party
  present : incidence ∈ relationIncidences input.law (origin input visit)
  port_exact : incidence.1 = port

abbrev Relation := (visit : Visit input) ×
  (ProgrammeFace.relations input.law (Registered.reader input).raw
    (ActualBirth.occurrence input visit)).GeneratedRelation

def Witness.relation {port : Port} (witness : Witness input port) : Relation input :=
  ⟨witness.visit,
    (ProgrammeFace.relations input.law (Registered.reader input).raw
      (ActualBirth.occurrence input witness.visit)).relationOf
        (ProgrammeFace.exactRelation input.law (Registered.reader input).raw
          (ActualBirth.occurrence input witness.visit) witness.incidence witness.present)⟩

private def here (visit : Visit input) (port : Port) : Option (Witness input port) :=
  match found : (relationIncidences input.law (origin input visit)).find?
      (fun incidence : Port × Party => decide (incidence.1 = port)) with
  | none => none
  | some incidence => some ⟨visit, incidence, List.mem_of_find?_eq_some found, by
      have checked := List.find?_some
        (p := fun seed : Port × Party => decide (seed.1 = port)) (a := incidence) found
      exact of_decide_eq_true checked⟩

private theorem here_isSome (visit : Visit input) (port : Port) (present : presentAt input visit port) :
    (here input visit port).isSome = true := by
  unfold here
  split
  · rename_i absent
    obtain ⟨incidence, member, same⟩ := present
    have impossible := List.find?_eq_none.mp absent incidence member
    exact False.elim (impossible (by simp only [same, decide_true]))
  · rfl

private def fold : {current : (Root.ProgrammeSource.V input).Current} →
    (root input).ReachableAt current → (port : Port) → Option (Witness input port)
  | _, .initial, port => here input (root input).initialVisit port
  | target, .step prior nextEq, port =>
      (fold prior port).orElse (fun _ => here input ⟨target, .step prior nextEq⟩ port)

def lookup (visit : Visit input) (port : Port) : Option (Witness input port) :=
  fold input visit.history port

theorem lookup_next (visit : Visit input) {next : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some next) (port : Port) :
    lookup input (visit.next nextEq) port =
      (lookup input visit port).orElse (fun _ => here input (visit.next nextEq) port) := rfl

theorem lookup_keeps_original_relation (visit : Visit input)
    {next : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some next)
    (port : Port) (witness : Witness input port) (found : lookup input visit port = some witness) :
    lookup input (visit.next nextEq) port = some witness := by
  rw [lookup_next, found]
  rfl

theorem original_incidence_generates_birth (visit : Visit input) (port : Port)
    (present : presentAt input visit port) : (lookup input visit port).isSome = true := by
  rcases visit with ⟨current, history⟩
  cases history with
  | initial => exact here_isSome input (root input).initialVisit port present
  | step prior nextEq =>
      change ((fold input prior port).orElse (fun _ => here input ⟨_, .step prior nextEq⟩ port)).isSome = true
      cases fold input prior port with
      | none => exact here_isSome input ⟨_, .step prior nextEq⟩ port present
      | some old => rfl

structure At (visit : Visit input) (port : Port) where
  private mk ::
  original : Witness input port
  generated : lookup input visit port = some original

def generate (visit : Visit input) (port : Port) (present : presentAt input visit port) : At input visit port :=
  ⟨(lookup input visit port).get (original_incidence_generates_birth input visit port present),
    (Option.some_get (original_incidence_generates_birth input visit port present)).symm⟩

def At.relation {visit : Visit input} {port : Port} (birth : At input visit port) : Relation input :=
  birth.original.relation input

def At.next {visit : Visit input} {port : Port} (birth : At input visit port)
    {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    At input (visit.next nextEq) port :=
  ⟨birth.original, lookup_keeps_original_relation input visit nextEq port birth.original birth.generated⟩

theorem At.next_keeps_original_generated_relation {visit : Visit input} {port : Port}
    (birth : At input visit port) {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    (birth.next input nextEq).relation input = birth.relation input := rfl

/-- Authority roles are source-state readouts of that retained relation.
They can change without replacing either its birth or any actor birth. -/
def At.role {visit : Visit input} {port : Port} (birth : At input visit port) : Party → Bool :=
  input.law.allowed (Root.ProgrammeSource.rawCurrent input visit.current).technology
    birth.original.incidence.1

theorem At.role_at_native_successor {visit : Visit input} {port : Port}
    (birth : At input visit port) {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    (birth.next input nextEq).role input =
      input.law.allowed (Root.ProgrammeSource.rawCurrent input target).technology port := by
  simp only [At.role, At.next, birth.original.port_exact]
  rfl

#print axioms generate
#print axioms At.next_keeps_original_generated_relation
#print axioms At.role_at_native_successor

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RelationHistory
