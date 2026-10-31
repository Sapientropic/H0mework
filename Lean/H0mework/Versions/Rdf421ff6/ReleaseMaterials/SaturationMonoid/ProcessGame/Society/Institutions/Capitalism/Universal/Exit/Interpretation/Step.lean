import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.SourceRelations.Policy

/-! The original joint-word compiler consumes a mixed original word:
shared production, personal needs and autonomous self-supply can coexist.
The relation family is a consumer parameter; the root supplies its actual
generated family, and classified control always takes precedence. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (family : OriginalItem law current word → List Port) (group : List Party)

def ExplainedPort (item : OriginalItem law current word) (port : Port) : Prop :=
  SharedAt law current word group item port ∨ PersonalUse.At law current word item port ∨
    AutonomousProduction.At law item.val

instance (item : OriginalItem law current word) (port : Port) :
    Decidable (ExplainedPort law current word group item port) := by unfold ExplainedPort; infer_instance

def UnexplainedAt (item : OriginalItem law current word) : Prop :=
  Blocked law current word group item ∨ Law.SourceRelations.OpaqueAt law item ∨
    ∃ port ∈ law.requiredPorts item.val.before item.val.request,
      port ∉ family item ∧ ¬ ExplainedPort law current word group item port

instance (item : OriginalItem law current word) :
    Decidable (UnexplainedAt law current word family group item) := by unfold UnexplainedAt; infer_instance

def Checks : Prop :=
  (∀ item : OriginalItem law current word,
    ¬ Blocked law current word group item ∧ ¬ Law.SourceRelations.OpaqueAt law item ∧
      ∀ port ∈ law.requiredPorts item.val.before item.val.request,
        port ∉ family item ∧ ExplainedPort law current word group item port) ∧
    Necessity.AllNeedsPaid law current group word

instance : Decidable (Checks law current word family group) := by
  unfold Checks
  exact decidable_of_iff
    ((∀ item ∈ (law.rawItems current word).attach,
      ¬ Blocked law current word group item ∧ ¬ Law.SourceRelations.OpaqueAt law item ∧
        ∀ port ∈ law.requiredPorts item.val.before item.val.request,
          port ∉ family item ∧ ExplainedPort law current word group item port) ∧
      Necessity.AllNeedsPaid law current group word)
    (by simp only [List.mem_attach, true_implies])

omit [DecidableEq Port] in
theorem classified_control_is_preserved (checked : Checks law current word family group)
    (use : ControlUse law current word family) : False :=
  (checked.1 use.item).2.2 use.port use.required |>.1 use.controlled

omit [DecidableEq Port] in
theorem source_step_is_exhaustive :
    Nonempty (ControlUse law current word family) ∨
      (∃ item, UnexplainedAt law current word family group item) ∨
      ¬ Necessity.AllNeedsPaid law current group word ∨ Checks law current word family group := by
  classical
  by_cases control : Nonempty (ControlUse law current word family)
  · exact Or.inl control
  right
  by_cases unknown : ∃ item, UnexplainedAt law current word family group item
  · exact Or.inl unknown
  right
  by_cases paid : Necessity.AllNeedsPaid law current group word
  · right
    refine ⟨?_, paid⟩
    intro item
    have clear : ¬ UnexplainedAt law current word family group item := fun h => unknown ⟨item, h⟩
    have unblocked : ¬ Blocked law current word group item := fun h => clear (Or.inl h)
    have accepted : law.Valid item.val.before item.val.request := by
      by_contra refused
      exact unblocked (Or.inl refused)
    refine ⟨unblocked, (fun opaquePolicy => clear (Or.inr (Or.inl opaquePolicy))), ?_⟩
    intro port required
    have absent : port ∉ family item := fun included => control ⟨⟨item, accepted, port, required, included⟩⟩
    exact ⟨absent, Classical.byContradiction (fun unexplained =>
      clear (Or.inr (Or.inr ⟨port, required, absent, unexplained⟩)))⟩
  · exact Or.inl paid

omit [DecidableEq Port] in
theorem checked_word_generates_paid_next (checked : Checks law current word family group) :
    ∃ alternative, law.jointWord group current word = some alternative ∧
      law.next current alternative = law.next current word ∧
      Necessity.AllNeedsPaid law current group alternative ∧
      (∀ item ∈ law.rawItems current alternative,
        law.Valid item.before item.request ∧ item.request.signer ∈ group ∧
          ∀ person ∈ item.request.consents, person ∈ group) ∧
      alternative.map Request.operation = word.map Request.operation := by
  have available : law.jointWord group current word ≠ none := by
    apply law.jointWord_complete
    intro item member
    have unblocked := (checked.1 ⟨item, member⟩).1
    refine ⟨Classical.byContradiction (fun refused => unblocked (Or.inl refused)), ?_⟩
    cases selected : law.jointSigner group item.before item.request with
    | none => exact False.elim (unblocked (Or.inr selected))
    | some signer =>
      obtain ⟨inside, valid⟩ := law.jointSigner_sound group _ _ signer selected
      exact ⟨signer, inside, valid⟩
  cases generated : law.jointWord group current word with
  | none => exact (available generated).elim
  | some alternative =>
    exact ⟨alternative, rfl, law.jointWord_same_next group current word _ generated,
      Necessity.allNeedsPaid_jointWord law current group word _ generated checked.2,
      (law.jointWord_sound group current word _ generated 0).2.1,
      (law.jointWord_sound group current word _ generated 0).2.2⟩

#print axioms source_step_is_exhaustive
#print axioms checked_word_generates_paid_next

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation
