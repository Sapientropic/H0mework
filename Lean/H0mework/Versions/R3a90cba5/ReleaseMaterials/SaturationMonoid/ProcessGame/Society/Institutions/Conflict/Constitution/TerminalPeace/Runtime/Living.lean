import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Factorization
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Replay
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.PeriodSafe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Shortage

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (normalise)
open Conflict.Consumers.Evolving (C R compact)
open Quantities.Execution
open ExposureGuard
open Material (livingWord livingInput)
open Original.Replay (stopCut stop_source stop_ready stop_review stop_raw)

noncomputable section

private def ownMeal (bearer : Bool) (request : R) : Bool :=
  match request with
  | ⟨signer, [], false, [], .use owner portions .necessity⟩ =>
    decide (signer = bearer ∧ owner = bearer ∧ portions = [(true, 1)])
  | _ => false

/-- Each person approves their own one-unit meal in the jointly submitted
food programme. Even inside that programme a substituted material item
cannot inherit the approval. -/
private def mealAnswers : OwnerAnswers Original.seed :=
  fun past input position bearer =>
    match input with
    | some (.execute [left, right]) =>
      ownMeal false left && ownMeal true right &&
        ownMeal bearer (originalItems (seed := Original.seed) past (some (.execute [left, right])))[position].request
    | _ => false

private theorem stop_snapshot : stopCut.raw = Original.snapshot 111 113 :=
  stop_raw.trans Original.cut_raw

private theorem meal_questions_are_personal (cut : C) (installed : cut.native.input = compact) :
    ∀ item ∈ (Physical.Public.interpreter compact).rawItems (Original.snapshot 111 113) livingWord,
      ∀ question ∈ questions cut item, ownMeal question.1 item.request = true := by
  unfold questions materialQuestions physical Boundary.Actual.materialLaw
  rw [installed]
  decide +kernel

private theorem meal_admission (past : Original.Word) (same : endAt Original.seed past = stopCut)
    (roster : List Bool) : Admitted roster mealAnswers past livingInput := by
  constructor
  · rw [same]
    exact Material.the_living_period_has_original_authority_at stopCut stop_source stop_snapshot stop_ready stop_review
  · intro position question asked _
    let item := (originalItems (seed := Original.seed) past livingInput)[position]
    have listed : item ∈ Boundary.Actual.items (endAt Original.seed past) livingInput := List.getElem_mem _
    rw [same, Material.the_living_periods_original_inventory_at stopCut stop_source stop_snapshot stop_ready stop_review] at listed
    have original : question ∈ questions stopCut item := by
      change question ∈ questions (endAt Original.seed past) item at asked
      rwa [same] at asked
    change ownMeal question.1 item.request = true
    exact meal_questions_are_personal stopCut stop_source item listed question original

/-- The exact word proposed after the installation's material-free write,
including the original accounting drain. -/
def protectedLivingPeriod : Original.Word := periodAndAccounting stopCut livingWord

private theorem accounting_item_is_empty (cut : C) (front later : Original.Word)
    (input : Reparation.Actual.Input Bool Bool Bool Unit Unit) (empty : inventory cut (front ++ input :: later) = []) :
    Boundary.Actual.items (endAt cut front) input = [] := by
  rw [show front ++ input :: later = front ++ ([input] ++ later) from rfl, inventory_append, inventory_append] at empty
  exact (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp empty).2).1

private theorem end_after_cons (cut : C) (input : Reparation.Actual.Input Bool Bool Bool Unit Unit)
    (front : Original.Word) : endAt cut (input :: front) = endAt (next cut input) front := rfl

private theorem each_living_input_is_admitted
    (start : WarVisit) (initial : endAt Original.seed start.history = stopCut)
    (front later : Original.Word) (input : Reparation.Actual.Input Bool Bool Bool Unit Unit)
    (original : protectedLivingPeriod = front ++ input :: later) (roster : List Bool) :
    Admitted roster mealAnswers (start.history ++ front) input ∧
      Boundary.Actual.damages (endAt Original.seed (start.history ++ front)) input Original.community = [] := by
  change livingInput :: drain (next stopCut livingInput) = front ++ input :: later at original
  cases front with
  | nil =>
    have selected := (List.cons.inj original).1
    subst input
    rw [List.append_nil]
    refine ⟨meal_admission start.history initial roster, ?_⟩
    rw [initial]
    exact Material.the_living_periods_material_body_is_damage_free_at stopCut stop_source stop_snapshot stop_ready stop_review
  | cons first front =>
    obtain ⟨rfl, rest⟩ := List.cons.inj original
    have drained := (the_first_exhausted_native_cut_is_the_original_paid_drain (next stopCut livingInput)).2.2.1
    have noneWritten : originalItems (seed := Original.seed) (start.history ++ livingInput :: front) input = [] := by
      change Boundary.Actual.items (endAt Original.seed (start.history ++ livingInput :: front)) input = []
      rw [endAt_append, initial, end_after_cons]
      rw [rest] at drained
      exact accounting_item_is_empty (next stopCut livingInput) front later input drained
    exact ⟨no_material_is_admitted roster mealAnswers _ input noneWritten,
      Boundary.Actual.no_material_write_has_no_damage _ _ _ noneWritten⟩

private def runMeal (prior : WarVisit) (word : Original.Word) : WarVisit :=
  word.foldl (fun visit input => visit.step mealAnswers (damageGate Original.community) openProbe input) prior

private theorem run_meal_keeps_the_original_word_and_ledger (prior : WarVisit) (word : Original.Word)
    (checks : ∀ (front later : Original.Word) input, word = front ++ input :: later → ∀ roster,
      Admitted roster mealAnswers (prior.history ++ front) input ∧
        Boundary.Actual.damages (endAt Original.seed (prior.history ++ front)) input Original.community = []) :
    (runMeal prior word).history = prior.history ++ word ∧
      (runMeal prior word).state.stack.balances = prior.state.stack.balances := by
  induction word generalizing prior with
  | nil => exact ⟨List.append_nil _ |>.symm, rfl⟩
  | cons input tail earlier =>
    let reached := prior.step mealAnswers (damageGate Original.community) openProbe input
    have approved := checks [] tail input rfl prior.roster
    rw [List.append_nil] at approved
    have selected := the_original_gate_keeps_every_safe_admissible_input
      (community := Original.community) (check := openProbe) approved.1 approved.2 rfl
    have exactStep : reached.history = prior.history ++ [input] := by
      change prior.history ++ (prior.verdict mealAnswers (damageGate Original.community) openProbe input).emitted = _
      rw [Visit.verdict, selected]
    have preserved := the_revised_visit_keeps_the_exact_original_reparation_portfolio prior mealAnswers openProbe input
    have later := earlier reached (by
      intro front later next listed roster
      rw [exactStep, List.append_assoc]
      exact checks (input :: front) later next (congrArg (input :: ·) listed) roster)
    exact ⟨later.1.trans (by rw [exactStep, List.append_assoc]; rfl), later.2.trans preserved⟩

private def mealSchedule : WarScheduler where
  lane := fun _ _ => .personal
  personal := fun tick _ => protectedLivingPeriod[tick]?.getD stop
  rival := fun _ _ => stop
  offer := fun _ _ _ => []

def paidLivingVisit : WarVisit :=
  run mealAnswers mealSchedule false (protectedLivingPeriod.length + 1)

private theorem the_schedule_reads_each_submitted_living_input (tick : Nat)
    (within : tick ≤ protectedLivingPeriod.length) :
    afterInstallation mealAnswers mealSchedule false tick =
      runMeal (firstWrite mealAnswers) (protectedLivingPeriod.take tick) := by
  induction tick with
  | zero => rfl
  | succ tick earlier =>
    have inside := Nat.lt_of_succ_le within
    have submitted : protectedLivingPeriod[tick]? = some protectedLivingPeriod[tick] :=
      List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
    change (afterInstallation mealAnswers mealSchedule false tick).step mealAnswers
      (damageGate Original.community) openProbe (protectedLivingPeriod[tick]?.getD stop) = _
    rw [earlier inside.le, submitted, Option.getD_some, List.take_succ_eq_append_getElem inside]
    simp only [runMeal, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem the_schedule_writes_the_complete_living_programme :
    paidLivingVisit = runMeal (firstWrite mealAnswers) protectedLivingPeriod := by
  unfold paidLivingVisit
  rw [every_raw_history_uses_the_same_original_first_write,
    the_schedule_reads_each_submitted_living_input _ le_rfl, List.take_length]

private theorem protected_period_really_runs :
    paidLivingVisit.history = (Original.history ++ [stop]) ++ protectedLivingPeriod ∧
      paidLivingVisit.state.stack.balances = [(Original.occurrence, Original.balance)] := by
  have initial := the_original_installation_writes_its_literal_first_input mealAnswers
  have source : endAt Original.seed (firstWrite mealAnswers).history = stopCut :=
    (congrArg (endAt Original.seed) initial).trans Original.Replay.stop_cut_is_the_original_extended_history
  have ran := run_meal_keeps_the_original_word_and_ledger (firstWrite mealAnswers) protectedLivingPeriod
    (each_living_input_is_admitted (firstWrite mealAnswers) source)
  rw [the_schedule_writes_the_complete_living_programme]
  exact ⟨ran.1.trans (congrArg (· ++ protectedLivingPeriod) initial),
    ran.2.trans ((the_revised_visit_keeps_the_exact_original_reparation_portfolio opening mealAnswers openProbe stop).trans
      Original.balances_exact)⟩

theorem the_protected_living_visit_uses_the_original_material_successor :
    endAt Original.seed paidLivingVisit.history = endAt stopCut protectedLivingPeriod := by
  rw [protected_period_really_runs.1, endAt_append, Original.Replay.stop_cut_is_the_original_extended_history]

private theorem paid_meal_guards : PeriodChecks stopCut livingWord :=
  Material.the_living_period_passes_the_original_guards_at stopCut stop_source stop_snapshot

private theorem protected_period_raw :
    (endAt stopCut protectedLivingPeriod).raw =
      (Physical.Public.interpreter compact).next (Original.snapshot 111 113) livingWord := by
  rw [protectedLivingPeriod, (the_original_paid_period_retains_all_native_rows stopCut livingWord stop_ready
    stop_review paid_meal_guards).2, stop_source, stop_snapshot, show normalise livingWord = livingWord from rfl]

private theorem protected_meal_delivers (bearer : Bool) :
    Quantities.Demand.delivered stopCut protectedLivingPeriod bearer .necessity true = 1 := by
  rw [Quantities.Demand.delivered_is_from_original_inventory, protectedLivingPeriod,
    inventory_of_the_original_period_and_accounting stopCut livingWord stop_ready stop_review paid_meal_guards,
    show stopCut.native.handlerFace.rootRead = Physical.Public.interpreter stopCut.native.input from rfl,
    stop_source, stop_snapshot, show normalise livingWord = livingWord from rfl]
  cases bearer <;> decide +kernel

/-- The same guarded visit performs the living write, consumes its native
accounting, and retains the original victim's exact six. -/
theorem the_protected_runtime_writes_one_original_living_period :
    paidLivingVisit.history = (Original.history ++ [stop]) ++ protectedLivingPeriod ∧
      Quantities.Recorded Original.seed paidLivingVisit.history ∧
      Quantities.Settled stopCut protectedLivingPeriod ∧
      (∀ bearer : Bool, Quantities.Demand.delivered stopCut protectedLivingPeriod bearer .necessity true = 1) ∧
      (endAt Original.seed paidLivingVisit.history).raw.clock = Original.cut.raw.clock + 1 ∧
      paidLivingVisit.state.stack.balances = [(Original.occurrence, Original.balance)] := by
  refine ⟨protected_period_really_runs.1, Quantities.record _ _,
    (the_original_paid_period_retains_all_native_rows stopCut livingWord stop_ready stop_review paid_meal_guards).1,
    protected_meal_delivers, ?_, protected_period_really_runs.2⟩
  rw [the_protected_living_visit_uses_the_original_material_successor, protected_period_raw, Original.cut_raw]
  decide +kernel

theorem the_protected_successor_cannot_deliver_food (suffix : Original.Word) (bearer : Bool) :
    Quantities.Demand.delivered (endAt Original.seed paidLivingVisit.history) suffix bearer .necessity true = 0 := by
  rw [the_protected_living_visit_uses_the_original_material_successor]
  refine Material.no_food_is_delivered_from_an_original_zero_stock_cut _ ((endAt_input _ _).trans stop_source)
    (Material.original_stock_stays_nonnegative stopCut protectedLivingPeriod (by
      rw [stop_raw]
      exact Material.the_original_stocks_are_nonnegative)) ?_ suffix bearer
  rw [protected_period_raw]
  decide +kernel

private theorem the_protected_successor_keeps_the_original_food_row (bearer : Bool) :
    (bearer, .necessity, true, (1 : ℚ)) ∈ Quantities.Demand.requirements (endAt Original.seed paidLivingVisit.history) := by
  rw [the_protected_living_visit_uses_the_original_material_successor,
    ← endAt_append Original.cut [stop] protectedLivingPeriod]
  exact Material.each_original_food_cell_survives_every_original_continuation ([stop] ++ protectedLivingPeriod) bearer

/-- Both original people still have their original living row. Every
continuation starts after their last actual food was consumed. -/
def the_protected_successor_has_a_named_food_shortage (suffix : Original.Word) (bearer : Bool) :
    Quantities.Demand.Deficit (endAt Original.seed paidLivingVisit.history) suffix where
  cell := (bearer, .necessity, true, 1)
  original := the_protected_successor_keeps_the_original_food_row bearer
  shortage := lt_of_eq_of_lt (the_protected_successor_cannot_deliver_food suffix bearer) (by norm_num)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
