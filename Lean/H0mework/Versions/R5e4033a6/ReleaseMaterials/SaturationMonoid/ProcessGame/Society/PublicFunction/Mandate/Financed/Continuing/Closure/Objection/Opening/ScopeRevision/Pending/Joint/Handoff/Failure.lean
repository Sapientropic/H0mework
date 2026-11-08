import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source

/-! Failed menus retain a concrete failed check. The emitted fallback has
its own actual failure, distinct from the other candidate words. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open Institutions.Capitalism.Universal.Source.Program Followup
noncomputable section
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Ready bound inputs)

def AllValid (before : Current) (word : List Action) : Prop :=
  ∀ item ∈ (law fresh).rawItems before word, (law fresh).Valid item.before item.request
instance (before : Current) (word : List Action) : Decidable (AllValid fresh before word) := by
  unfold AllValid; infer_instance

def Checks (before : Current) (word : List Action) : Prop :=
  AllValid fresh before word ∧ ServiceAdequate (law fresh) before fresh.task word ∧
    (decodePaidOpening fresh before word).isSome = true ∧
    MaterialHealthy before

inductive Failure (before : Current) (word : List Action) where
  | private refused (item : {item // item ∈ (law fresh).rawItems before word})
      (denied : ¬ (law fresh).Valid item.val.before item.val.request)
  | private service (legal : AllValid fresh before word)
      (unpaid : ¬ ServiceAdequate (law fresh) before fresh.task word)
  | private opening (legal : AllValid fresh before word)
      (paid : ServiceAdequate (law fresh) before fresh.task word)
      (absent : decodePaidOpening fresh before word = none)

  | private stock (legal : AllValid fresh before word)
      (paid : ServiceAdequate (law fresh) before fresh.task word)
      (opening : (decodePaidOpening fresh before word).isSome = true)
      (unhealthy : ¬ MaterialHealthy before)

inductive FailureKind where
  | refused | service | opening | stock
  deriving DecidableEq

def Failure.kind {before : Current} {word : List Action} : Failure fresh before word → FailureKind
  | .refused .. => .refused
  | .service .. => .service
  | .opening .. => .opening
  | .stock .. => .stock

def failure (before : Current) (word : List Action) (failed : ¬ Checks fresh before word) : Failure fresh before word := by
  let items := ((law fresh).rawItems before word).attach
  cases found : items.find? (fun item => decide (¬ (law fresh).Valid item.val.before item.val.request)) with
  | some item =>
      exact .refused item (of_decide_eq_true (List.find?_some
        (p := fun item : {item // item ∈ (law fresh).rawItems before word} =>
          decide (¬ (law fresh).Valid item.val.before item.val.request)) found))
  | none =>
      have legal : AllValid fresh before word := by
        intro item member
        by_contra denied
        have inside : (⟨item,member⟩ : {item // item ∈ (law fresh).rawItems before word}) ∈ items :=
          List.mem_attach _ _
        have rejected := List.find?_eq_none.mp found _ inside
        rw [decide_eq_true denied] at rejected
        exact rejected rfl
      by_cases paid : ServiceAdequate (law fresh) before fresh.task word
      · cases opening : decodePaidOpening fresh before word with
        | none => exact .opening legal paid opening
        | some certificate =>
          have present : (decodePaidOpening fresh before word).isSome = true := by rw [opening]; rfl
          by_cases healthy : MaterialHealthy before
          · exact False.elim (failed ⟨legal,paid,present,healthy⟩)
          · exact .stock legal paid present healthy
      · exact .service legal paid

theorem Failure.failed_check {before : Current} {word : List Action} (evidence : Failure fresh before word) :
    ¬ Checks fresh before word := by
  intro accepted
  cases evidence
  next item denied => exact denied (accepted.1 item.val item.property)
  next legal unpaid => exact unpaid accepted.2.1
  next legal paid absent =>
    have present := accepted.2.2.1
    rw [absent] at present
    cases present
  next legal paid opening unhealthy => exact unhealthy accepted.2.2.2

def failedMethod (absent : select fresh (start fresh) = none) (method : Method) (listed : method ∈ methods) :
    Failure fresh (start fresh) (candidate fresh (start fresh) method) :=
  failure fresh _ _ (blocked_menu_has_actual_failed_checks fresh _ absent method listed)

theorem blocked_actual_word_has_a_failed_check (absent : select fresh (start fresh) = none) :
    ¬ Checks fresh (actual fresh 1).before (actual fresh 1).submitted := by
  rw [first_word_is_actually_emitted, first_word_uses_the_actual_start]
  have same : firstWord fresh = candidate fresh (start fresh) .productive := by
    simp only [firstWord,emitAt,absent,Option.map_none,Option.getD_none]
  rw [same]
  exact blocked_menu_has_actual_failed_checks fresh _ absent .productive (by simp [methods])

def actualFailure (absent : select fresh (start fresh) = none) :
    Failure fresh (actual fresh 1).before (actual fresh 1).submitted :=
  failure fresh _ _ (blocked_actual_word_has_a_failed_check fresh absent)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
