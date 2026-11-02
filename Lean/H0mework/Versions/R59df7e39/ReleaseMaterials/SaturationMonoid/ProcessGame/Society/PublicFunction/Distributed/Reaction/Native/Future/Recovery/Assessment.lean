import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Evaluation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Feedback Distributed.Recall.Information.Agency.Protocol

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (oldDepth : Nat)

structure Report where
  consumed : Nat
  evaluation : Evaluation old.source.code

variable {old oldDepth}

def report {target : Authority.Sources old.base old.scope} {count : Nat} {word : List (Action old)}
    {receipt : Receipt old oldDepth target count word} (made : Output receipt)
    (sameCode : target.val.code = old.source.code) : Report old :=
  ⟨made.walk.finish.consumed.length,sameCode ▸ made.evaluation⟩

def reportFrom {target : Authority.Sources old.base old.scope} {count : Nat} {word : List (Action old)}
    {receipt : Receipt old oldDepth target count word} (made : Output receipt) (start : Nat)
    (sameCode : target.val.code = old.source.code) : Report old :=
  ⟨made.walk.finish.consumed.length,sameCode ▸ made.evaluationFrom start⟩

theorem the_earlier_report_is_read_from_its_actual_installed_output
    {target : Authority.Sources old.base old.scope} {count : Nat} {word : List (Action old)}
    {receipt : Receipt old oldDepth target count word} (made : Output receipt) (start : Nat)
    (sameCode : target.val.code = old.source.code) : reportFrom made.read start sameCode = reportFrom made start sameCode := by
  rw [made.read_exact]

theorem the_report_is_read_from_its_actual_installed_output
    {target : Authority.Sources old.base old.scope} {count : Nat} {word : List (Action old)}
    {receipt : Receipt old oldDepth target count word} (made : Output receipt)
    (sameCode : target.val.code = old.source.code) : report made.read sameCode = report made sameCode := by
  rw [made.read_exact]

variable (old oldDepth)

def generate (source : SameCodeTarget old) (count : Nat) (word : List (Action old)) : Option (Report old) :=
  match Future.produce old oldDepth source.indexed count word with
  | .inl _ => none
  | .inr receipt => some (report (produce receipt) source.property)

theorem every_registered_capability_has_an_actual_complete_report
    (source : SameCodeTarget old) (count : Nat) (word : List (Action old))
    (inside : word ∈ capabilities old oldDepth) :
    ∃ actual, generate old oldDepth source count word = some actual := by
  have legal := (capability_is_available_and_legal word inside).2
  unfold generate Future.produce
  rw [dif_pos legal]
  exact ⟨_,rfl⟩

/-- Refused attempts remain visible. A complete or legal old result may not become
    incomplete or illegal, and paying for more progress never erases a cost axis. -/
def NoWorse (new previous : Report old) : Prop :=
  previous.consumed ≤ new.consumed ∧
  (previous.evaluation.legal = true → new.evaluation.legal = true) ∧
  (previous.evaluation.complete = true → new.evaluation.complete = true) ∧
  new.evaluation.profile = previous.evaluation.profile ∧
  Feedback.Authority.Trace.Lawful.NoWorse new.evaluation.native previous.evaluation.native ∧
  ∀ axis ∈ Window.axes old oldDepth, new.evaluation.value axis ≤ previous.evaluation.value axis

instance (new previous : Report old) : Decidable (NoWorse old oldDepth new previous) := by
  unfold NoWorse
  infer_instance

theorem noWorse_refl (actual : Report old) : NoWorse old oldDepth actual actual :=
  ⟨Nat.le_refl _,id,id,rfl,Feedback.Authority.Trace.Lawful.refl _,fun _ _ => le_refl _⟩

theorem noWorse_trans {first middle last : Report old}
    (left : NoWorse old oldDepth first middle) (right : NoWorse old oldDepth middle last) :
    NoWorse old oldDepth first last :=
  ⟨right.1.trans left.1,fun yes => left.2.1 (right.2.1 yes),
    fun yes => left.2.2.1 (right.2.2.1 yes),left.2.2.2.1.trans right.2.2.2.1,
    Feedback.Authority.Trace.Lawful.trans left.2.2.2.2.1 right.2.2.2.2.1,
    fun axis inside => (left.2.2.2.2.2 axis inside).trans (right.2.2.2.2.2 axis inside)⟩

def strict (new previous : Report old) : Prop :=
  NoWorse old oldDepth new previous ∧ ¬ NoWorse old oldDepth previous new

instance (new previous : Report old) : Decidable (strict old oldDepth new previous) := by
  unfold strict
  infer_instance

def compare (new previous : SameCodeTarget old) (newCount previousCount : Nat) (word : List (Action old)) : Bool :=
  match generate old oldDepth new newCount word,generate old oldDepth previous previousCount word with
  | some current,some original => decide (NoWorse old oldDepth current original)
  | _,_ => false

def allCapabilities (new previous : SameCodeTarget old) (newCount previousCount : Nat) : Bool :=
  (capabilities old oldDepth).all (compare old oldDepth new previous newCount previousCount)

theorem allCapabilities_iff (new previous : SameCodeTarget old) (newCount previousCount : Nat) :
    allCapabilities old oldDepth new previous newCount previousCount = true ↔
      ∀ word ∈ capabilities old oldDepth,
        ∃ current original,generate old oldDepth new newCount word = some current ∧
          generate old oldDepth previous previousCount word = some original ∧ NoWorse old oldDepth current original := by
  simp only [allCapabilities,List.all_eq_true]
  apply forall_congr'
  intro word
  apply forall_congr'
  intro inside
  obtain ⟨current,now⟩ := every_registered_capability_has_an_actual_complete_report old oldDepth new newCount word inside
  obtain ⟨original,previousResult⟩ := every_registered_capability_has_an_actual_complete_report old oldDepth previous previousCount word inside
  simp only [compare,now,previousResult,decide_eq_true_eq]
  constructor
  · exact fun valid => ⟨current,original,rfl,rfl,valid⟩
  · rintro ⟨a,b,ha,hb,valid⟩
    have sa := Option.some.inj ha
    have sb := Option.some.inj hb
    cases sa;cases sb;exact valid

theorem allCapabilities_refl (source : SameCodeTarget old) (count : Nat) :
    allCapabilities old oldDepth source source count count = true := by
  apply (allCapabilities_iff _ _ _ _ _ _).mpr
  intro word inside
  obtain ⟨actual,generated⟩ := every_registered_capability_has_an_actual_complete_report old oldDepth source count word inside
  exact ⟨actual,actual,generated,generated,noWorse_refl _ _ _⟩

theorem allCapabilities_trans (first middle last : SameCodeTarget old) (firstCount middleCount lastCount : Nat)
    (left : allCapabilities old oldDepth first middle firstCount middleCount = true)
    (right : allCapabilities old oldDepth middle last middleCount lastCount = true) :
    allCapabilities old oldDepth first last firstCount lastCount = true := by
  apply (allCapabilities_iff _ _ _ _ _ _).mpr
  intro word inside
  obtain ⟨a,b,ha,hb,ab⟩ := (allCapabilities_iff _ _ _ _ _ _).mp left word inside
  obtain ⟨c,d,hc,hd,cd⟩ := (allCapabilities_iff _ _ _ _ _ _).mp right word inside
  have same := Option.some.inj (hb.symm.trans hc)
  cases same
  exact ⟨a,d,ha,hd,noWorse_trans _ _ ab cd⟩

structure Failure (new previous : SameCodeTarget old) (newCount previousCount : Nat) where
  word : List (Action old)
  registered : word ∈ capabilities old oldDepth
  broken : compare old oldDepth new previous newCount previousCount word ≠ true

def inspect (new previous : SameCodeTarget old) (newCount previousCount : Nat) :
    PLift (allCapabilities old oldDepth new previous newCount previousCount = true) ⊕
      Failure old oldDepth new previous newCount previousCount :=
  match Distributed.inspect (fun word => compare old oldDepth new previous newCount previousCount word = true)
      (capabilities old oldDepth) with
  | .accepted checked => .inl ⟨List.all_eq_true.mpr checked⟩
  | .rejected word registered broken => .inr ⟨word,registered,broken⟩

theorem failure_is_an_actual_complete_responsibility_violation
    (new previous : SameCodeTarget old) (newCount previousCount : Nat)
    (failed : Failure old oldDepth new previous newCount previousCount) :
    ∃ current original,generate old oldDepth new newCount failed.word = some current ∧
      generate old oldDepth previous previousCount failed.word = some original ∧
      ¬ NoWorse old oldDepth current original := by
  obtain ⟨current,now⟩ := every_registered_capability_has_an_actual_complete_report old oldDepth new newCount failed.word failed.registered
  obtain ⟨original,prior⟩ := every_registered_capability_has_an_actual_complete_report old oldDepth previous previousCount failed.word failed.registered
  refine ⟨current,original,now,prior,?_⟩
  intro valid
  apply failed.broken
  simp only [compare,now,prior,decide_eq_true_eq]
  exact valid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment
