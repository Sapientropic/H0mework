import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Qualification

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v w x

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Candidate : Type u} {Index : Type v} {Issue : Index → Candidate → Type w} {Address : Type x}

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (compile : Candidate → List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (check : (index : Index) → (candidate : Candidate) → Option (Issue index candidate))
  (read : Candidate → Address → EReal)

abbrev values : Set (Address → EReal) :=
  Bounds.Compiled.values source compile (System.inspect check) read

theorem an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it
    (amounts : Address → EReal) :
    amounts ∈ values source compile check read ↔
      ∃ candidate, Settled source (compile candidate) ∧ Passes check candidate ∧ read candidate = amounts := by
  change (∃ candidate, Settled source (compile candidate) ∧ inspect check candidate = none ∧ read candidate = amounts) ↔ _
  simp only [all_checks_pass_exactly_when_there_is_no_failure]

theorem original_joint_envelope_is_tight :
    IsGLB (values source compile check read) (sInf (values source compile check read)) ∧
      IsLUB (values source compile check read) (sSup (values source compile check read)) :=
  ⟨isGLB_sInf _, isLUB_sSup _⟩

theorem every_coordinate_resolves_on_the_same_joint_feasible_domain (address : Address) :
    Bounds.Compiled.Minimum source compile (inspect check) (fun candidate => read candidate address) ∧
    Bounds.Compiled.Minimum source compile (inspect check)
      (fun candidate => (OrderDual.toDual (read candidate address))) :=
  ⟨Bounds.Compiled.resolve _ _ _ _, Bounds.Compiled.resolve _ _ _ _⟩

inductive BoxIssue (limit : Address → EReal) (candidate : Candidate) : Type _
  | original (issue : Obstruction source (compile candidate))
  | requirement (issue : Failure check candidate)
  | address (address : Address) (short : limit address < read candidate address)

theorem BoxIssue.refutes {limit : Address → EReal} {candidate : Candidate}
    (issue : BoxIssue source compile check read limit candidate) :
    ¬ (Settled source (compile candidate) ∧ Passes check candidate ∧ read candidate ≤ limit) := by
  rintro ⟨paid, passes, fit⟩
  cases issue with
  | original missing => exact missing.refutes paid.toFeasible
  | requirement failed =>
    have impossible := (passes failed.1).symm.trans failed.2.2
    cases impossible
  | address address short => exact (not_le_of_gt short) (fit address)

inductive BoxDecision (limit : Address → EReal) : Type _
  | paid (candidate : Candidate) (paid : Settled source (compile candidate)) (pass : Passes check candidate)
      (inside : read candidate ≤ limit)
  | blocked (originalIssues : ∀ candidate, Recorded source (compile candidate) ∧
      Nonempty (BoxIssue source compile check read limit candidate))

/-- Budget feasibility is a property of one actual paid assignment. Every
failed candidate retains its own account and at least one exact obstruction. -/
def decideBox (limit : Address → EReal) : BoxDecision source compile check read limit := by
  classical
  by_cases feasible : ∃ candidate, Settled source (compile candidate) ∧ Passes check candidate ∧ read candidate ≤ limit
  · let chosen := Classical.choose feasible
    have paid := Classical.choose_spec feasible
    exact .paid chosen paid.1 paid.2.1 paid.2.2
  · refine .blocked fun candidate => ⟨record source (compile candidate), ?_⟩
    cases decideAt source (compile candidate) with
    | blocked original => exact ⟨.original original⟩
    | feasible original =>
      cases seen : inspect check candidate with
      | some issue => exact ⟨.requirement issue⟩
      | none =>
        have passes := (all_checks_pass_exactly_when_there_is_no_failure check candidate).mp seen
        have exceeds : ¬ ∀ address, read candidate address ≤ limit address :=
          fun fits => feasible ⟨candidate, settle source _ original, passes, fits⟩
        obtain ⟨address, short⟩ := not_forall.mp exceeds
        exact ⟨.address address (lt_of_not_ge short)⟩

theorem a_joint_box_is_paid_or_has_an_exact_original_issue_for_every_plan (limit : Address → EReal) :
    (∃ amounts ∈ values source compile check read, amounts ≤ limit) ∨
      ∀ candidate, Recorded source (compile candidate) ∧ Nonempty (BoxIssue source compile check read limit candidate) := by
  cases decideBox source compile check read limit with
  | blocked every => exact .inr every
  | paid candidate paid passed inside =>
    exact .inl ⟨read candidate, (an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it
      source compile check read _).mpr ⟨candidate, paid, passed, rfl⟩, inside⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System
