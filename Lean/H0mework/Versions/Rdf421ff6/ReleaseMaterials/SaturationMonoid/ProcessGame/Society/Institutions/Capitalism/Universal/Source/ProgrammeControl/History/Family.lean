import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Detector

/-! Completed necessary circuits and fresh control uses are distinct
readouts.  Historical identity alone never emits a current control use;
the present original item must actually call the port for an excluded
recipient or operator.  A fresh completed circuit is indexed by its
original access ordinal, so later uses of an old bulk lot are not new access. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program Kernel.AssetAuthority
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Source beneficiaries and operators of this actually executed item.
A name appearing elsewhere in the social cohort is not enough. -/
def affectedSubjects (item : ExecutionItem Party Good Port Technology Instrument) : List Party :=
  ((input.law.actualCredit item.before item.request).filterMap
    (fun lot => if 0 < lot.2 then some lot.1.1 else none) ++
  match item.request.operation with
  | .produce operator => [operator]
  | .use bearer _ kind => if kind = .necessity ∨ kind = .maintenance then [bearer] else []
  | .issue _ debtor _ quantity => if 0 < quantity then [debtor] else []
  | .assign _ _ sender _ quantity => if 0 < quantity then [sender] else []
  | _ => []).dedup

def FreshControl (port : Port) (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  input.law.Valid item.before item.request ∧
  port ∈ input.law.requiredPorts item.before item.request ∧
  ∃ subject ∈ affectedSubjects input item, PrivatePhase input.law item.before port subject

instance (port : Port) (item : ExecutionItem Party Good Port Technology Instrument) :
    Decidable (FreshControl input port item) := by unfold FreshControl; infer_instance

def generatedFamily (visit : Visit input) (item : RootFace.Item input visit) : List Port :=
  (Discovery.discovered input (actual input visit)).filterMap (fun capital =>
    if FreshControl input capital.access.port item.val then some capital.access.port else none)

theorem generatedFamily_actual_control (visit : Visit input) (item : RootFace.Item input visit)
    (port : Port) (member : port ∈ generatedFamily input visit item) :
    ∃ capital ∈ Discovery.discovered input (actual input visit),
      capital.access.port = port ∧ FreshControl input port item.val := by
  obtain ⟨capital, generated, found⟩ := List.mem_filterMap.mp member
  split at found
  · rename_i checked
    exact ⟨capital, generated, Option.some.inj found, (Option.some.inj found) ▸ checked⟩
  · contradiction

def controlUse (visit : Visit input) (item : RootFace.Item input visit) (port : Port)
    (member : port ∈ generatedFamily input visit item) :
    ControlUse input.law (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current) (generatedFamily input visit) :=
  let found := generatedFamily_actual_control input visit item port member
  ⟨item, found.choose_spec.2.2.1, port, found.choose_spec.2.2.2.1, member⟩

/-- No authority is emitted merely because a port once belonged to a
capital circuit.  The current affected subject must face actual exclusion. -/
theorem self_supply_cannot_reuse_old_exclusion (visit : Visit input)
    (item : RootFace.Item input visit) (port : Port)
    (ownAccess : ∀ subject ∈ affectedSubjects input item.val,
      input.law.allowed item.val.before.technology port subject = true) :
    port ∉ generatedFamily input visit item := by
  intro member
  obtain ⟨_, _, _, _, _, subject, present, excluded⟩ :=
    generatedFamily_actual_control input visit item port member
  have allowed := ownAccess subject present
  exact Bool.noConfusion (allowed.symm.trans excluded.2)

/-- `cutoff` is an ordinal in this same finite original history, not a new
clock or root.  Every returned circuit contains a genuinely new access. -/
def completedSince (endpoint : Visit input) (cutoff : Nat) : List (Capital input endpoint) :=
  (Discovery.discovered input endpoint).filter (fun capital => decide (cutoff ≤ capital.access.access.position input))

theorem completedSince_has_original_new_access (endpoint : Visit input) (cutoff : Nat)
    (capital : Capital input endpoint) (member : capital ∈ completedSince input endpoint cutoff) :
    cutoff ≤ capital.access.access.position input ∧
    (capital.access.access.origin input).instruction? input = some (capital.access.access.raw input) ∧
    (capital.access.need.origin input).instruction? input = some (capital.access.need.raw input) := by
  exact ⟨of_decide_eq_true (List.mem_filter.mp member).2,
    (capital.access.access.original_visit_and_local_index input).2.2,
    (capital.access.need.original_visit_and_local_index input).2.2⟩

theorem old_access_cannot_be_counted_again (endpoint : Visit input) (cutoff : Nat)
    (capital : Capital input endpoint) (old : capital.access.access.position input < cutoff) :
    capital ∉ completedSince input endpoint cutoff := by
  intro member
  exact Nat.not_le_of_lt old (completedSince_has_original_new_access input endpoint cutoff capital member).1

omit [DecidableEq Port] [DecidableEq Instrument] in
/-- If a prior recipient becomes the actual holder, the original port can
still be private for a different actual participant.  No old recipient is
hard-coded into the current control predicate. -/
theorem holder_rotation_uses_current_subject (port : Port)
    (item : ExecutionItem Party Good Port Technology Instrument) (subject : Party)
    (accepted : input.law.Valid item.before item.request)
    (required : port ∈ input.law.requiredPorts item.before item.request)
    (present : subject ∈ affectedSubjects input item)
    (phase : PrivatePhase input.law item.before port subject) : FreshControl input port item :=
  ⟨accepted, required, subject, present, phase⟩

#print axioms generatedFamily_actual_control
#print axioms controlUse
#print axioms self_supply_cannot_reuse_old_exclusion
#print axioms completedSince_has_original_new_access
#print axioms old_access_cannot_be_counted_again

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
