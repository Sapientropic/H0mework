import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Source
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)

structure Tensor where
  present : Evaluation cursor.source.val.code
  restoration : (word : List (Future.Recovery.Action cursor.model)) →
    Option (Future.Recovery.Assessment.Report cursor.model ×
      Option (Future.Recovery.Funding.Failure cursor.model cursor.depth word))

abbrev Tensor.future (value : Tensor cursor) (word : List (Future.Recovery.Action cursor.model)) :=
  (value.restoration word).map Prod.fst
abbrev Tensor.funding (value : Tensor cursor) (word : List (Future.Recovery.Action cursor.model)) :=
  (value.restoration word).bind Prod.snd

def tensor (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) : Tensor cursor :=
  ⟨present cursor term rival n,restoration cursor pricing term rival n⟩

def futureNoWorse : Option (Future.Recovery.Assessment.Report cursor.model) →
    Option (Future.Recovery.Assessment.Report cursor.model) → Prop
  | some current,some previous => Future.Recovery.Assessment.NoWorse cursor.model cursor.depth current previous
  | _,_ => False
instance (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    Decidable (futureNoWorse cursor new previous) := by
  cases new <;> cases previous <;> unfold futureNoWorse <;> infer_instance

def accepts (new previous : Tensor cursor) : Prop :=
  Synthesis.accepts cursor.source.val.code (Window.axes cursor.model cursor.depth) new.present previous.present ∧
  (∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,
    futureNoWorse cursor (new.future cursor word) (previous.future cursor word)) ∧
  ∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,
    (previous.funding cursor word).isNone = true → (new.funding cursor word).isNone = true
instance (new previous : Tensor cursor) : Decidable (accepts cursor new previous) := by
  unfold accepts;infer_instance

theorem futureNoWorse_trans {first middle last : Option (Future.Recovery.Assessment.Report cursor.model)}
    (left : futureNoWorse cursor first middle) (right : futureNoWorse cursor middle last) :
    futureNoWorse cursor first last := by
  cases first <;> cases middle <;> cases last <;> simp only [futureNoWorse] at *
  all_goals first | contradiction | exact Future.Recovery.Assessment.noWorse_trans _ _ left right

theorem accepts_trans {first middle last : Tensor cursor}
    (left : accepts cursor first middle) (right : accepts cursor middle last) : accepts cursor first last :=
  ⟨Synthesis.accepts_trans _ _ _ _ _ left.1 right.1,
    fun word inside => futureNoWorse_trans cursor (left.2.1 word inside) (right.2.1 word inside),
    fun word inside funded => left.2.2 word inside (right.2.2 word inside funded)⟩

/-- Admission and archive identity constrain admissibility. They cannot create a strict dividend. -/
def evaluationBenefit (new previous : Evaluation cursor.source.val.code) : Prop :=
  (previous.legal = true → new.legal = true) ∧
  (previous.complete = true → new.complete = true) ∧
  (Feedback.Authority.Trace.Lawful.inventory new.native).due.Subperm
    (Feedback.Authority.Trace.Lawful.inventory previous.native).due ∧
  ∀ axis ∈ Window.axes cursor.model cursor.depth, new.value axis ≤ previous.value axis
instance (new previous : Evaluation cursor.source.val.code) : Decidable (evaluationBenefit cursor new previous) := by
  unfold evaluationBenefit;infer_instance

theorem evaluationBenefit_refl (value : Evaluation cursor.source.val.code) : evaluationBenefit cursor value value :=
  ⟨id,id,List.Subperm.refl _,fun _ _ => le_refl _⟩
theorem evaluationBenefit_trans {first middle last : Evaluation cursor.source.val.code}
    (left : evaluationBenefit cursor first middle) (right : evaluationBenefit cursor middle last) :
    evaluationBenefit cursor first last :=
  ⟨fun yes => left.1 (right.1 yes),fun yes => left.2.1 (right.2.1 yes),
    left.2.2.1.trans right.2.2.1,fun axis inside => (left.2.2.2 axis inside).trans (right.2.2.2 axis inside)⟩

def futureBenefit : Option (Future.Recovery.Assessment.Report cursor.model) →
    Option (Future.Recovery.Assessment.Report cursor.model) → Prop
  | some current,some previous => previous.consumed ≤ current.consumed ∧
      evaluationBenefit cursor current.evaluation previous.evaluation
  | _,none => True
  | none,some _ => False
instance (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    Decidable (futureBenefit cursor new previous) := by
  cases new <;> cases previous <;> unfold futureBenefit <;> infer_instance

theorem futureBenefit_refl (value : Option (Future.Recovery.Assessment.Report cursor.model)) :
    futureBenefit cursor value value := by
  cases value with
  | none => trivial
  | some value => exact ⟨Nat.le_refl _,evaluationBenefit_refl cursor _⟩
theorem futureBenefit_trans {first middle last : Option (Future.Recovery.Assessment.Report cursor.model)}
    (left : futureBenefit cursor first middle) (right : futureBenefit cursor middle last) :
    futureBenefit cursor first last := by
  cases first <;> cases middle <;> cases last <;> simp only [futureBenefit] at *
  all_goals first | trivial | contradiction |
    exact ⟨right.1.trans left.1,evaluationBenefit_trans cursor left.2 right.2⟩

def benefit (new previous : Tensor cursor) : Prop :=
  evaluationBenefit cursor new.present previous.present ∧
  (∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,
    futureBenefit cursor (new.future cursor word) (previous.future cursor word)) ∧
  ∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,
    (previous.funding cursor word).isNone = true → (new.funding cursor word).isNone = true
instance (new previous : Tensor cursor) : Decidable (benefit cursor new previous) := by
  unfold benefit;infer_instance

theorem benefit_refl (value : Tensor cursor) : benefit cursor value value :=
  ⟨evaluationBenefit_refl cursor _,fun _ _ => futureBenefit_refl cursor _,fun _ _ yes => yes⟩
theorem benefit_trans {first middle last : Tensor cursor}
    (left : benefit cursor first middle) (right : benefit cursor middle last) : benefit cursor first last :=
  ⟨evaluationBenefit_trans cursor left.1 right.1,
    fun word inside => futureBenefit_trans cursor (left.2.1 word inside) (right.2.1 word inside),
    fun word inside funded => left.2.2 word inside (right.2.2 word inside funded)⟩

theorem acceptance_bounds_every_real_benefit {new previous : Tensor cursor}
    (accepted : accepts cursor new previous) : benefit cursor new previous := by
  refine ⟨⟨fun _ => accepted.1.1,fun _ => accepted.1.2.1,accepted.1.2.2.2.1.2,
    accepted.1.2.2.2.2⟩,?_,accepted.2.2⟩
  intro word inside
  have checked := accepted.2.1 word inside
  cases a : new.future cursor word <;> cases b : previous.future cursor word <;>
    simp only [futureNoWorse,a,b] at checked
  all_goals first | contradiction |
    exact ⟨checked.1,checked.2.1,checked.2.2.1,checked.2.2.2.2.1.2,checked.2.2.2.2.2⟩

variable (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
  (n : Nat)

theorem the_joint_table_preserves_every_native_recovery_and_funding_row
    (term : Term cursor) (rival : Opponent cursor.source.val.code) (bounded : n ≤ cursor.state.remaining) :
    tensor cursor pricing term (opponent cursor (restrict cursor rival)) n = tensor cursor pricing term rival n := by
  exact congrArg₂ (fun present restore => (⟨present,restore⟩ : Tensor cursor))
    (complete_evaluation_is_jointly_covered cursor term rival n bounded)
    (congrArg (fun words => restorationWords cursor pricing words n)
      (one_joint_table_preserves_every_forecast_word cursor term rival n bounded))

theorem finite_comparison_iff_every_same_adaptive_opponent
    (relation : Tensor cursor → Tensor cursor → Prop) (new previous : Term cursor)
    (bounded : n ≤ cursor.state.remaining) :
    (∀ table ∈ tables cursor, relation (tensor cursor pricing new (opponent cursor table) n)
      (tensor cursor pricing previous (opponent cursor table) n)) ↔
    ∀ rival : Opponent cursor.source.val.code, relation (tensor cursor pricing new rival n)
      (tensor cursor pricing previous rival n) := by
  constructor
  · intro finite rival
    have checked := finite (restrict cursor rival) (restriction_is_generated cursor rival)
    rw [the_joint_table_preserves_every_native_recovery_and_funding_row cursor pricing n new rival bounded,
      the_joint_table_preserves_every_native_recovery_and_funding_row cursor pricing n previous rival bounded] at checked
    exact checked
  · intro all table _;exact all _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning
