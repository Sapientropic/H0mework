import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.SourceFamily
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

/-! Joint production need not grant every member control of everybody
else's personal consumption.  This readout explains an actual self-signed
necessary use, after classified capital use has taken priority.  It does
not interpret an opaque policy guard as an independence certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.PersonalUse

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

def At (item : OriginalItem law current word) (port : Port) : Prop :=
  match item.val.request.operation with
  | .use bearer goods kind =>
      (kind = .necessity ∨ kind = .maintenance) ∧
      item.val.request.signer = bearer ∧ item.val.request.consents = [] ∧
      law.controller item.val.before.technology port = bearer ∧
      port ∈ goods.map (fun lot => law.stockPort item.val.before.technology bearer lot.1) ∧
      law.Valid item.val.before item.val.request
  | _ => False

instance (item : OriginalItem law current word) (port : Port) :
    Decidable (At law current word item port) := by
  unfold At
  cases item.val.request.operation <;> infer_instance

omit [DecidableEq Port] in
theorem original_bearer_really_uses_source_need (item : OriginalItem law current word) (port : Port)
    (personal : At law current word item port) :
    ∃ bearer goods kind,
      item.val.request.operation = .use bearer goods kind ∧
      item.val.request.signer = bearer ∧ item.val.request.consents = [] ∧
      law.controller item.val.before.technology port = bearer ∧
      ((kind = .necessity ∧ goods = law.necessities item.val.before bearer) ∨
       (kind = .maintenance ∧ goods = law.mandatoryMaintenance item.val.before bearer)) ∧
      law.actualDebit item.val.before item.val.request = locate bearer goods := by
  cases operation : item.val.request.operation with
  | use bearer goods kind =>
      simp only [At, operation] at personal
      have valid := personal.2.2.2.2.2
      have guard := valid.2.2.1
      refine ⟨bearer, goods, kind, rfl, personal.2.1, personal.2.2.1, personal.2.2.2.1, ?_, ?_⟩
      · rcases personal.1 with necessity | maintenance
        · left
          exact ⟨necessity, by simpa only [RawLaw.ClaimGuard, operation, necessity] using guard⟩
        · right
          exact ⟨maintenance, by simpa only [RawLaw.ClaimGuard, operation, maintenance] using guard⟩
      · simp only [RawLaw.actualDebit, if_pos valid, RawLaw.debit, operation]
  | _ => simp only [At, operation] at personal

variable (localAttempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
  (group : List Party)

def ExplainedAt (item : OriginalItem law current word) : Prop :=
  law.Valid item.val.before item.val.request ∧
  ∀ port ∈ law.requiredPorts item.val.before item.val.request,
    port ∉ generatedFamily law current word localAttempts item ∧
      (SharedAt law current word group item port ∨ At law current word item port)

instance (item : OriginalItem law current word) :
    Decidable (ExplainedAt law current word localAttempts group item) := by
  unfold ExplainedAt
  infer_instance

def UnexplainedAt (item : OriginalItem law current word) : Prop :=
  Blocked law current word group item ∨
    ∃ port ∈ law.requiredPorts item.val.before item.val.request,
      port ∉ generatedFamily law current word localAttempts item ∧
      ¬ SharedAt law current word group item port ∧ ¬ At law current word item port

instance (item : OriginalItem law current word) :
    Decidable (UnexplainedAt law current word localAttempts group item) := by
  unfold UnexplainedAt
  infer_instance

def unexplained : List { item : OriginalItem law current word //
    UnexplainedAt law current word localAttempts group item } :=
  (law.rawItems current word).attach.filterMap (fun item =>
    if pending : UnexplainedAt law current word localAttempts group item then some ⟨item, pending⟩ else none)

def Checks : Prop :=
  (∀ item : OriginalItem law current word, ExplainedAt law current word localAttempts group item) ∧
    Exit.Necessity.AllNeedsPaid law current group word

instance : Decidable (Checks law current word localAttempts group) := by
  unfold Checks
  exact decidable_of_iff
    ((∀ item ∈ (law.rawItems current word).attach,
      ExplainedAt law current word localAttempts group item) ∧
      Exit.Necessity.AllNeedsPaid law current group word)
    (by simp only [List.mem_attach, true_implies])

structure PaidJointProgramme where
  private mk ::
  alternative : RawEvent Party Good Port Technology Instrument
  checked : Checks law current word localAttempts group
  generated : law.jointWord group current word = some alternative

def compile : Option (PaidJointProgramme law current word localAttempts group) :=
  if checked : Checks law current word localAttempts group then
    match generated : law.jointWord group current word with
    | none => none
    | some alternative => some ⟨alternative, checked, generated⟩
  else none

theorem checks_and_joint_word_generate
    (checks : Checks law current word localAttempts group)
    (available : law.jointWord group current word ≠ none) :
    ∃ programme, compile law current word localAttempts group = some programme := by
  cases generated : law.jointWord group current word with
  | none => exact False.elim (available generated)
  | some alternative =>
      refine ⟨⟨alternative, checks, generated⟩, ?_⟩
      simp only [compile, dif_pos checks]
      split
      · rename_i absent
        exact False.elim (available absent)
      · rename_i word found
        have same := Option.some.inj (found.symm.trans generated)
        subst word
        rfl

theorem cleared_original_word_generates
    (noControl : ¬ Nonempty (ControlUse law current word (generatedFamily law current word localAttempts)))
    (clear : ∀ item : OriginalItem law current word,
      ¬ UnexplainedAt law current word localAttempts group item)
    (paid : Exit.Necessity.AllNeedsPaid law current group word) :
    ∃ programme, compile law current word localAttempts group = some programme := by
  have accepted : ∀ item : OriginalItem law current word, law.Valid item.val.before item.val.request := by
    intro item
    by_contra refused
    exact clear item (Or.inl (Or.inl refused))
  have checks : Checks law current word localAttempts group := by
    refine ⟨?_, paid⟩
    intro item
    refine ⟨accepted item, ?_⟩
    intro port required
    have absent : port ∉ generatedFamily law current word localAttempts item := by
      intro included
      exact noControl ⟨⟨item, accepted item, port, required, included⟩⟩
    refine ⟨absent, ?_⟩
    by_cases shared : SharedAt law current word group item port
    · exact Or.inl shared
    · right
      by_contra personal
      exact clear item (Or.inr ⟨port, required, absent, shared, personal⟩)
  have available : law.jointWord group current word ≠ none := by
    apply law.jointWord_complete
    intro item member
    refine ⟨accepted ⟨item, member⟩, ?_⟩
    cases generated : law.jointSigner group item.before item.request with
    | none => exact False.elim (clear ⟨item, member⟩ (Or.inl (Or.inr generated)))
    | some signer =>
        obtain ⟨inside, valid⟩ := law.jointSigner_sound group _ _ signer generated
        exact ⟨signer, inside, valid⟩
  exact checks_and_joint_word_generate law current word localAttempts group checks available

theorem classified_C_cannot_be_erased (programme : PaidJointProgramme law current word localAttempts group)
    (use : ControlUse law current word (generatedFamily law current word localAttempts)) : False :=
  (programme.checked.1 use.item).2 use.port use.required |>.1 use.controlled

theorem generated_full_need_and_complete_next
    (programme : PaidJointProgramme law current word localAttempts group) :
    law.next current programme.alternative = law.next current word ∧
    Exit.Necessity.AllNeedsPaid law current group programme.alternative ∧
    ∀ item ∈ law.rawItems current programme.alternative,
      law.Valid item.before item.request ∧ item.request.signer ∈ group ∧
        ∀ person ∈ item.request.consents, person ∈ group :=
  ⟨law.jointWord_same_next group current word _ programme.generated,
    Exit.Necessity.allNeedsPaid_jointWord law current group word _ programme.generated programme.checked.2,
    (law.jointWord_sound group current word _ programme.generated 0).2.1⟩

#print axioms original_bearer_really_uses_source_need
#print axioms compile
#print axioms classified_C_cannot_be_erased
#print axioms generated_full_need_and_complete_next

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.PersonalUse
