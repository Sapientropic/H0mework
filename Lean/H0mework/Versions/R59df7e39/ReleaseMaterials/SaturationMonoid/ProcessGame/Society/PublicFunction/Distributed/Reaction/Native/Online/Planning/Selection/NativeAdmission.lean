import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit.Budget
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
open NativeBenefit
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Typed identity operands retain the native archive, finance and control sources.
    Primitive equality and operand acquisition remain separate native work. -/
inductive Atom (Party Good Port Technology Instrument : Type) where
  | native (value : NativeKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  | construction (value : NativeInventory.Event Party Good Port Technology Instrument)
  | debt (value : Identity.DebtImage Party Good Port (Mandate.State Party Technology) Instrument)
  | quantity (value : ℚ)
  | service (value : Option Nat)
  | control (value : Open.Control (Mandate.State Party Technology))
  deriving DecidableEq

abbrev Key := Atom Party Good Port Technology Instrument

def encodedEqual {α Key : Type} [DecidableEq Key] (encode : α → Key) (faithful : Function.Injective encode)
    (left right : α) : Check Key (left = right) :=
  transport ⟨fun same => faithful same,fun same => congrArg encode same⟩ (equal (encode left) (encode right))

def listsEqual {α Key : Type} (test : (left right : α) → Check Key (left = right)) :
    (left right : List α) → Check Key (left = right)
  | [],[] => transport (by simp) (boolean true)
  | [],_::_ | _::_,[] => transport (by simp) (boolean false)
  | left::ls,right::rs => transport (by simp only [List.cons.injEq])
      (conjunction (test left right) (fun _ => listsEqual test ls rs))

def listsBudget {α : Type} (budget : α → α → Nat) : List α → List α → Nat
  | left::ls,right::rs => budget left right+1+listsBudget budget ls rs
  | _,_ => 1

theorem lists_work_bound {α Key : Type} (test : (left right : α) → Check Key (left = right))
    (budget : α → α → Nat) (bounded : ∀ left right,(test left right).work.length ≤ budget left right)
    (left right : List α) : (listsEqual test left right).work.length ≤ listsBudget budget left right := by
  induction left generalizing right with
  | nil => cases right <;> simp [listsEqual,transport,boolean,listsBudget]
  | cons head tail ih =>
    cases right with
    | nil => simp [listsEqual,transport,boolean,listsBudget]
    | cons other rest =>
      have bound := conjunction_work_bound (test head other) (fun _ => listsEqual test tail rest)
      have a := bounded head other
      have b := ih rest
      change (conjunction (test head other) (fun _ => listsEqual test tail rest)).work.length ≤ _
      change _ ≤ budget head other+1+listsBudget budget tail rest
      omega

variable {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)
abbrev Profile := Settlement.Profile Party Good Port (Mandate.State Party Technology) Instrument

private def debtEqual := encodedEqual (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) Atom.debt (by intro a b h;cases h;rfl)
private def quantityEqual := encodedEqual (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) Atom.quantity (by intro a b h;cases h;rfl)
private def serviceEqual := encodedEqual (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) Atom.service (by intro a b h;cases h;rfl)
private def controlEqual := encodedEqual (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) Atom.control (by intro a b h;cases h;rfl)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem profile_iff (new previous : Profile (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    (new.originalDebts = previous.originalDebts ∧ new.newbornDebts = previous.newbornDebts ∧
      new.rights = previous.rights ∧ new.uncoveredClaims = previous.uncoveredClaims ∧
      new.firstServices = previous.firstServices ∧ new.control = previous.control) ↔ new = previous := by
  cases new;cases previous;simp only [Settlement.Profile.mk.injEq]

def profile (new previous : Profile (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (new = previous) :=
  transport (profile_iff new previous)
    (conjunction (listsEqual (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.originalDebts previous.originalDebts) (fun _ =>
      conjunction (listsEqual (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.newbornDebts previous.newbornDebts) (fun _ =>
        conjunction (listsEqual (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) new.rights previous.rights) (fun _ =>
          conjunction (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.uncoveredClaims previous.uncoveredClaims) (fun _ =>
            conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ =>
              (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control))))))

def profileBudget (new previous : Profile (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Nat :=
  listsBudget (fun _ _ => 1) new.originalDebts previous.originalDebts +
  listsBudget (fun _ _ => 1) new.newbornDebts previous.newbornDebts +
  listsBudget (listsBudget (fun _ _ => 1)) new.rights previous.rights +
  listsBudget (fun _ _ => 1) new.uncoveredClaims previous.uncoveredClaims +
  listsBudget (fun _ _ => 1) new.firstServices previous.firstServices + 6

theorem profile_work_bound (new previous : Profile (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    (profile new previous).work.length ≤ profileBudget new previous := by
  have a := lists_work_bound (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (fun _ _ => Nat.le_refl _) new.originalDebts previous.originalDebts
  have b := lists_work_bound (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (fun _ _ => Nat.le_refl _) new.newbornDebts previous.newbornDebts
  have c := lists_work_bound (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) (listsBudget (fun _ _ => 1))
    (lists_work_bound (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (fun _ _ => Nat.le_refl _)) new.rights previous.rights
  have d := lists_work_bound (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (fun _ _ => Nat.le_refl _) new.uncoveredClaims previous.uncoveredClaims
  have e := lists_work_bound (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (fun _ _ => Nat.le_refl _) new.firstServices previous.firstServices
  have step0 := conjunction_work_bound (listsEqual (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.originalDebts previous.originalDebts) (fun _ => conjunction (listsEqual (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.newbornDebts previous.newbornDebts) (fun _ => conjunction (listsEqual (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) new.rights previous.rights) (fun _ => conjunction (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.uncoveredClaims previous.uncoveredClaims) (fun _ => conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control)))))
  have step1 := conjunction_work_bound (listsEqual (debtEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.newbornDebts previous.newbornDebts) (fun _ => conjunction (listsEqual (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) new.rights previous.rights) (fun _ => conjunction (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.uncoveredClaims previous.uncoveredClaims) (fun _ => conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control))))
  have step2 := conjunction_work_bound (listsEqual (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) new.rights previous.rights) (fun _ => conjunction (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.uncoveredClaims previous.uncoveredClaims) (fun _ => conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control)))
  have step3 := conjunction_work_bound (listsEqual (quantityEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.uncoveredClaims previous.uncoveredClaims) (fun _ => conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control))
  have step4 := conjunction_work_bound (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control)
  change (profile new previous).work.length ≤ _ at step0
  change (conjunction (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices) (fun _ => (controlEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.control previous.control)).work.length ≤ (listsEqual (serviceEqual (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) new.firstServices previous.firstServices).work.length+1+1 at step4
  unfold profileBudget
  omega

def inventory (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (Feedback.Authority.Trace.Lawful.NoWorse new previous) :=
  let current := NativeInventory.compile new
  let original := NativeInventory.compile previous
  record ((current.work ++ original.work).map (fun event => .source (.construction event)))
    (transport (by rw [current.exact,original.exact];rfl)
      (rekey Atom.native (by intro a b h;cases h;rfl)
        (conjunction (subperm original.inventory.admitted current.inventory.admitted) (fun _ =>
          subperm current.inventory.due original.inventory.due))))

def inventoryBudget (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) : Nat :=
  NativeInventory.budget new + NativeInventory.budget previous +
    (subpermBudget (NativeInventory.rowCount previous) (NativeInventory.rowCount new) + 1 +
    subpermBudget (NativeInventory.rowCount new) (NativeInventory.rowCount previous))

theorem inventory_work_bound (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    (inventory new previous).work.length ≤ inventoryBudget new previous := by
  have a := subperm_work_bound (NativeInventory.compile previous).inventory.admitted (NativeInventory.compile new).inventory.admitted
  have b := subperm_work_bound (NativeInventory.compile new).inventory.due (NativeInventory.compile previous).inventory.due
  have c := conjunction_work_bound (subperm (NativeInventory.compile previous).inventory.admitted (NativeInventory.compile new).inventory.admitted)
    (fun _ => subperm (NativeInventory.compile new).inventory.due (NativeInventory.compile previous).inventory.due)
  have bound := c.trans (Nat.add_le_add (Nat.add_le_add_right a 1) b)
  simp only [inventory,record,transport,rekey,List.length_append,List.length_map]
  rw [NativeInventory.work_exact,NativeInventory.work_exact]
  rw [(NativeInventory.compile new).exact,(NativeInventory.compile previous).exact] at bound
  rw [(NativeInventory.compile new).exact,(NativeInventory.compile previous).exact]
  unfold inventoryBudget
  have admitted := subpermBudget_mono (Nat.le_of_eq (NativeInventory.admitted_length previous))
    (Nat.le_of_eq (NativeInventory.admitted_length new))
  have due := subpermBudget_mono (NativeInventory.due_length_bound new) (NativeInventory.due_length_bound previous)
  exact Nat.add_le_add_left (bound.trans (Nat.add_le_add (Nat.add_le_add_right admitted 1) due)) _

def economics (new previous : Evaluation cursor.source.val.code) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (∀ axis ∈ Window.axes cursor.model cursor.depth,new.value axis ≤ previous.value axis) :=
  allRows (fun axis => new.value axis ≤ previous.value axis)
    (fun axis => rationalLe (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth)

theorem economics_work_bound (new previous : Evaluation cursor.source.val.code) :
    (economics cursor new previous).work.length ≤ 2*(Window.axes cursor.model cursor.depth).length := by
  have bound := allRows_work_bound (fun axis => new.value axis ≤ previous.value axis)
    (fun axis => rationalLe (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (new.value axis) (previous.value axis))
    (fun _ => 1) (fun _ => Nat.le_refl _) (Window.axes cursor.model cursor.depth)
  simpa [economics,List.sum_replicate,Nat.mul_comm] using bound

def present (new previous : Evaluation cursor.source.val.code) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (Synthesis.accepts cursor.source.val.code (Window.axes cursor.model cursor.depth) new previous) :=
  conjunction (boolean new.legal) (fun _ =>
    conjunction (boolean new.complete) (fun _ =>
      conjunction (profile new.profile previous.profile) (fun _ =>
        conjunction (inventory new.native previous.native) (fun _ =>
          economics cursor new previous))))

def presentBudget (new previous : Evaluation cursor.source.val.code) :=
  6+profileBudget new.profile previous.profile+inventoryBudget new.native previous.native+2*(Window.axes cursor.model cursor.depth).length

theorem present_work_bound (new previous : Evaluation cursor.source.val.code) :
    (present cursor new previous).work.length ≤ presentBudget cursor new previous := by
  have a := profile_work_bound new.profile previous.profile
  have b := inventory_work_bound new.native previous.native
  have c := economics_work_bound cursor new previous
  have step0 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (boolean new.legal) (fun _ => conjunction (boolean new.complete) (fun _ => conjunction (profile new.profile previous.profile) (fun _ => conjunction (inventory new.native previous.native) (fun _ => economics cursor new previous))))
  have step1 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (boolean new.complete) (fun _ => conjunction (profile new.profile previous.profile) (fun _ => conjunction (inventory new.native previous.native) (fun _ => economics cursor new previous)))
  have step2 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (profile new.profile previous.profile) (fun _ => conjunction (inventory new.native previous.native) (fun _ => economics cursor new previous))
  have step3 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (inventory new.native previous.native) (fun _ => economics cursor new previous)
  change (present cursor new previous).work.length ≤ 1+1+_ at step0
  change _ ≤ 1+1+_ at step1
  unfold presentBudget
  omega

def report (new previous : Future.Recovery.Assessment.Report cursor.model) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (Future.Recovery.Assessment.NoWorse cursor.model cursor.depth new previous) :=
  conjunction (naturalLe previous.consumed new.consumed) (fun _ =>
    conjunction (implication (boolean previous.evaluation.legal) (fun _ => boolean new.evaluation.legal)) (fun _ =>
      conjunction (implication (boolean previous.evaluation.complete) (fun _ => boolean new.evaluation.complete)) (fun _ =>
        conjunction (profile new.evaluation.profile previous.evaluation.profile) (fun _ =>
          conjunction (inventory new.evaluation.native previous.evaluation.native) (fun _ =>
            economics cursor new.evaluation previous.evaluation)))))

def reportBudget (new previous : Future.Recovery.Assessment.Report cursor.model) :=
  12+profileBudget new.evaluation.profile previous.evaluation.profile+
    inventoryBudget new.evaluation.native previous.evaluation.native+2*(Window.axes cursor.model cursor.depth).length

theorem report_work_bound (new previous : Future.Recovery.Assessment.Report cursor.model) :
    (report cursor new previous).work.length ≤ reportBudget cursor new previous := by
  have a := profile_work_bound new.evaluation.profile previous.evaluation.profile
  have b := inventory_work_bound new.evaluation.native previous.evaluation.native
  have c := economics_work_bound cursor new.evaluation previous.evaluation
  have legal := implication_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (boolean previous.evaluation.legal) (fun _ => boolean new.evaluation.legal)
  have complete := implication_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (boolean previous.evaluation.complete) (fun _ => boolean new.evaluation.complete)
  change _ ≤ 3 at legal
  change _ ≤ 3 at complete
  have step0 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (naturalLe previous.consumed new.consumed) (fun _ => conjunction (implication (boolean previous.evaluation.legal) (fun _ => boolean new.evaluation.legal)) (fun _ => conjunction (implication (boolean previous.evaluation.complete) (fun _ => boolean new.evaluation.complete)) (fun _ => conjunction (profile new.evaluation.profile previous.evaluation.profile) (fun _ => conjunction (inventory new.evaluation.native previous.evaluation.native) (fun _ => economics cursor new.evaluation previous.evaluation)))))
  have step1 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (implication (boolean previous.evaluation.legal) (fun _ => boolean new.evaluation.legal)) (fun _ => conjunction (implication (boolean previous.evaluation.complete) (fun _ => boolean new.evaluation.complete)) (fun _ => conjunction (profile new.evaluation.profile previous.evaluation.profile) (fun _ => conjunction (inventory new.evaluation.native previous.evaluation.native) (fun _ => economics cursor new.evaluation previous.evaluation))))
  have step2 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (implication (boolean previous.evaluation.complete) (fun _ => boolean new.evaluation.complete)) (fun _ => conjunction (profile new.evaluation.profile previous.evaluation.profile) (fun _ => conjunction (inventory new.evaluation.native previous.evaluation.native) (fun _ => economics cursor new.evaluation previous.evaluation)))
  have step3 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (profile new.evaluation.profile previous.evaluation.profile) (fun _ => conjunction (inventory new.evaluation.native previous.evaluation.native) (fun _ => economics cursor new.evaluation previous.evaluation))
  have step4 := conjunction_work_bound (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (inventory new.evaluation.native previous.evaluation.native) (fun _ => economics cursor new.evaluation previous.evaluation)
  change (report cursor new previous).work.length ≤ 1+1+_ at step0
  unfold reportBudget
  omega

def future (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (Planning.futureNoWorse cursor new previous) :=
  match new,previous with
  | some current,some original =>
      transport (by simp [Planning.futureNoWorse]) (conjunction (boolean true) (fun _ => report cursor current original))
  | none,none | some _,none | none,some _ => transport (by simp [Planning.futureNoWorse]) (boolean false)

def futureBudget (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :=
  match new,previous with
  | some current,some original => reportBudget cursor current original+2
  | _,_ => 1

theorem future_work_bound (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (future cursor new previous).work.length ≤ futureBudget cursor new previous := by
  cases new with
  | none => cases previous <;> simp [future,transport,boolean,futureBudget]
  | some current =>
    cases previous with
    | none => simp [future,transport,boolean,futureBudget]
    | some original =>
      have bound := conjunction_work_bound (boolean (Key := Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) true) (fun _ => report cursor current original)
      have inside := report_work_bound cursor current original
      change (conjunction (boolean true) (fun _ => report cursor current original)).work.length ≤ _
      change _ ≤ 1+1+_ at bound
      dsimp only [futureBudget]
      omega

def funding {α : Type} (new previous : Option α) : Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (previous.isNone = true → new.isNone = true) :=
  implication (boolean previous.isNone) (fun _ => boolean new.isNone)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem funding_work_bound {α : Type} (new previous : Option α) :
    (funding (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) new previous).work.length ≤ 3 :=
  implication_work_bound _ _

theorem present_is_the_original_admission (new previous : Evaluation cursor.source.val.code) :
    (present cursor new previous).value = decide (Synthesis.accepts cursor.source.val.code (Window.axes cursor.model cursor.depth) new previous) := by
  unfold Check.value
  exact congrArg (fun d => @decide _ d) (Subsingleton.elim _ _)

theorem future_is_the_original_admission (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (future cursor new previous).value = decide (Planning.futureNoWorse cursor new previous) := by
  unfold Check.value
  exact congrArg (fun d => @decide _ d) (Subsingleton.elim _ _)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
