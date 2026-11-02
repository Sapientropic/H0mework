import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.ActionWork
open Institutions.Capitalism.Universal.Source.Program

/-- Field values remain typed operands; equality internals remain native obligations. -/
inductive Atom (Party Good Port Technology Instrument : Type) where
  | party (value : Party)
  | good (value : Good)
  | port (value : Port)
  | technology (value : Technology)
  | instrument (value : Instrument)
  | quantity (value : ℚ)
  deriving DecidableEq

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
abbrev Key := Atom Party Good Port Technology Instrument

def party (left right : Party) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.party (by intro a b same;cases same;rfl) left right

theorem party_work_bound (left right : Party) : (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

def good (left right : Good) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.good (by intro a b same;cases same;rfl) left right

theorem good_work_bound (left right : Good) : (good (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

def port (left right : Port) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.port (by intro a b same;cases same;rfl) left right

theorem port_work_bound (left right : Port) : (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

def technology (left right : Technology) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.technology (by intro a b same;cases same;rfl) left right

theorem technology_work_bound (left right : Technology) : (technology (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

def instrument (left right : Instrument) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.instrument (by intro a b same;cases same;rfl) left right

theorem instrument_work_bound (left right : Instrument) : (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

def quantity (left right : ℚ) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeAdmission.encodedEqual Atom.quantity (by intro a b same;cases same;rfl) left right

theorem quantity_work_bound (left right : ℚ) : (quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := Nat.le_refl 1

private def tag {P : Prop} (made : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) P) := NativeBenefit.record [.boolean true] made
omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem tag_bound {P : Prop} (made : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) P) (budget : Nat)
    (bounded : made.work.length ≤ budget) : (tag made).work.length ≤ 1+budget := by
  simpa only [tag,NativeBenefit.record,List.length_append,List.length_singleton] using Nat.add_le_add_left bounded 1
omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem pair_bound {P Q : Prop} (first : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) P)
    (later : Unit → NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) Q) (a b : Nat)
    (left : first.work.length ≤ a) (right : (later ()).work.length ≤ b) :
    (NativeBenefit.conjunction first later).work.length ≤ a+1+b :=
  (NativeBenefit.conjunction_work_bound first later).trans (by omega)

def useKind : (left right : Use) → NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right)
  | .necessity,.necessity => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | .necessity,.maintenance => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .necessity,.investment => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .necessity,.contribution => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .necessity,.external => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .maintenance,.necessity => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .maintenance,.maintenance => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | .maintenance,.investment => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .maintenance,.contribution => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .maintenance,.external => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .investment,.necessity => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .investment,.maintenance => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .investment,.investment => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | .investment,.contribution => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .investment,.external => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .contribution,.necessity => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .contribution,.maintenance => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .contribution,.investment => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .contribution,.contribution => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | .contribution,.external => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .external,.necessity => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .external,.maintenance => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .external,.investment => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .external,.contribution => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .external,.external => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem useKind_work_bound (left right : Use) : (useKind (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 1 := by
  cases left <;> cases right <;> exact Nat.le_refl 1

def item (left right : Good × ℚ) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  NativeBenefit.transport (by cases left;cases right;simp only [Prod.mk.injEq])
    (NativeBenefit.conjunction (good (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.1 right.1) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.2 right.2))
theorem item_work_bound (left right : Good × ℚ) : (item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ 3 :=
  pair_bound _ _ 1 1 (good_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.1 right.1) (quantity_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.2 right.2)

def bundle (left right : Bundle Good) := NativeAdmission.listsEqual (item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right
def bundleBudget (left right : Bundle Good) := NativeAdmission.listsBudget (fun _ _ => 3) left right
theorem bundle_work_bound (left right : Bundle Good) : (bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ bundleBudget left right :=
  NativeAdmission.lists_work_bound (item (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 3) (item_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right

def parties (left right : List Party) := NativeAdmission.listsEqual (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right
def partiesBudget (left right : List Party) := NativeAdmission.listsBudget (fun _ _ => 1) left right
theorem parties_work_bound (left right : List Party) : (parties (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ partiesBudget left right :=
  NativeAdmission.lists_work_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right

def ports (left right : List Port) := NativeAdmission.listsEqual (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right
def portsBudget (left right : List Port) := NativeAdmission.listsBudget (fun _ _ => 1) left right
theorem ports_work_bound (left right : List Port) : (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ portsBudget left right :=
  NativeAdmission.lists_work_bound (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (fun _ _ => 1) (port_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) left right

def operation : (left right : Operation Party Good Technology Instrument) → NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right)
  | .produce actorL,.produce actorR => tag (NativeBenefit.transport (by simp only [Operation.produce.injEq]) (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR))
  | .transfer senderL recipientL goodsL,.transfer senderR recipientR goodsR => tag (NativeBenefit.transport (by simp only [Operation.transfer.injEq]) (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR))))
  | .use actorL goodsL purposeL,.use actorR goodsR purposeR => tag (NativeBenefit.transport (by simp only [Operation.use.injEq]) (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => NativeBenefit.conjunction (bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (fun _ => useKind (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) purposeL purposeR))))
  | .issue instrumentL issuerL beneficiaryL quantityL,.issue instrumentR issuerR beneficiaryR quantityR => tag (NativeBenefit.transport (by simp only [Operation.issue.injEq]) (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)))))
  | .assign instrumentL issuerL senderL recipientL quantityL,.assign instrumentR issuerR senderR recipientR quantityR => tag (NativeBenefit.transport (by simp only [Operation.assign.injEq]) (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))))))
  | .settle instrumentL debtorL creditorL quantityL,.settle instrumentR debtorR creditorR quantityR => tag (NativeBenefit.transport (by simp only [Operation.settle.injEq]) (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) debtorL debtorR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)))))
  | .revise actorL technologyL,.revise actorR technologyR => tag (NativeBenefit.transport (by simp only [Operation.revise.injEq]) (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => technology (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) technologyL technologyR)))
  | .present,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | .produce _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .produce _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .transfer _ _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .use _ _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .issue _ _ _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .assign _ _ _ _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .settle _ _ _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .revise _ _,.present => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.produce _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.transfer _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.use _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.issue _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.assign _ _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.settle _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .present,.revise _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)

def operationBudget : Operation Party Good Technology Instrument → Operation Party Good Technology Instrument → Nat
  | .produce _,.produce _ => 1+1
  | .transfer _ _ goodsL,.transfer _ _ goodsR => 1+(1+1+(1+1+bundleBudget goodsL goodsR))
  | .use _ goodsL _,.use _ goodsR _ => 1+(1+1+(bundleBudget goodsL goodsR+1+1))
  | .issue _ _ _ _,.issue _ _ _ _ => 1+(1+1+(1+1+(1+1+1)))
  | .assign _ _ _ _ _,.assign _ _ _ _ _ => 1+(1+1+(1+1+(1+1+(1+1+1))))
  | .settle _ _ _ _,.settle _ _ _ _ => 1+(1+1+(1+1+(1+1+1)))
  | .revise _ _,.revise _ _ => 1+(1+1+1)
  | _,_ => 1

theorem operation_work_bound (left right : Operation Party Good Technology Instrument) :
    (operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left right).work.length ≤ operationBudget left right := by
  cases left <;> cases right
  · rename_i actorL actorR
    change (tag (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR)).work.length ≤ 1+1
    exact tag_bound _ _ (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR)
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i senderL recipientL goodsL senderR recipientR goodsR
    change (tag (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR)))).work.length ≤ 1+(1+1+(1+1+bundleBudget goodsL goodsR))
    exact tag_bound _ _ (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR)) (1) ((1+1+bundleBudget goodsL goodsR)) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (1) (bundleBudget goodsL goodsR) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (bundle_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR)))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i actorL goodsL purposeL actorR goodsR purposeR
    change (tag (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => NativeBenefit.conjunction (bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (fun _ => useKind (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) purposeL purposeR)))).work.length ≤ 1+(1+1+(bundleBudget goodsL goodsR+1+1))
    exact tag_bound _ _ (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => NativeBenefit.conjunction (bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (fun _ => useKind (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) purposeL purposeR)) (1) ((bundleBudget goodsL goodsR+1+1)) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (pair_bound (bundle (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (fun _ => useKind (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) purposeL purposeR) (bundleBudget goodsL goodsR) (1) (bundle_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) goodsL goodsR) (useKind_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) purposeL purposeR)))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i instrumentL issuerL beneficiaryL quantityL instrumentR issuerR beneficiaryR quantityR
    change (tag (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))))).work.length ≤ 1+(1+1+(1+1+(1+1+1)))
    exact tag_bound _ _ (pair_bound (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))) (1) ((1+1+(1+1+1))) (instrument_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)) (1) ((1+1+1)) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR) (1) (1) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) beneficiaryL beneficiaryR) (quantity_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i instrumentL issuerL senderL recipientL quantityL instrumentR issuerR senderR recipientR quantityR
    change (tag (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)))))).work.length ≤ 1+(1+1+(1+1+(1+1+(1+1+1))))
    exact tag_bound _ _ (pair_bound (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)))) (1) ((1+1+(1+1+(1+1+1)))) (instrument_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))) (1) ((1+1+(1+1+1))) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) issuerL issuerR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)) (1) ((1+1+1)) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) senderL senderR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR) (1) (1) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) recipientL recipientR) (quantity_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)))))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i instrumentL debtorL creditorL quantityL instrumentR debtorR creditorR quantityR
    change (tag (NativeBenefit.conjunction (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) debtorL debtorR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))))).work.length ≤ 1+(1+1+(1+1+(1+1+1)))
    exact tag_bound _ _ (pair_bound (instrument (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) debtorL debtorR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))) (1) ((1+1+(1+1+1))) (instrument_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) instrumentL instrumentR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) debtorL debtorR) (fun _ => NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR)) (1) ((1+1+1)) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) debtorL debtorR) (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (fun _ => quantity (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR) (1) (1) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) creditorL creditorR) (quantity_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) quantityL quantityR))))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · rename_i actorL technologyL actorR technologyR
    change (tag (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => technology (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) technologyL technologyR))).work.length ≤ 1+(1+1+1)
    exact tag_bound _ _ (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (fun _ => technology (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) technologyL technologyR) (1) (1) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) actorL actorR) (technology_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) technologyL technologyR))
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1
  · exact Nat.le_refl 1

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem request_iff (left right : Request Party Good Port Technology Instrument) :
    (left.signer = right.signer ∧ left.consents = right.consents ∧ left.purpose = right.purpose ∧ left.gates = right.gates ∧ left.operation = right.operation) ↔ left = right := by
  cases left;cases right;simp only [Request.mk.injEq]

def compare (left right : Request Party Good Port Technology Instrument) : NativeBenefit.Check (Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (left = right) :=
  tag (NativeBenefit.transport (request_iff left right) (NativeBenefit.conjunction (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.signer right.signer) (fun _ => NativeBenefit.conjunction (parties (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.consents right.consents) (fun _ => NativeBenefit.conjunction (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.purpose right.purpose) (fun _ => NativeBenefit.conjunction (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (fun _ => operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation))))))
def budget (left right : Request Party Good Port Technology Instrument) := 1+(1+1+(partiesBudget left.consents right.consents+1+(1+1+(portsBudget left.gates right.gates+1+operationBudget left.operation right.operation))))
theorem work_bound (left right : Request Party Good Port Technology Instrument) :
    (compare left right).work.length ≤ budget left right := by
  exact tag_bound _ _ (pair_bound (party (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.signer right.signer) (fun _ => NativeBenefit.conjunction (parties (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.consents right.consents) (fun _ => NativeBenefit.conjunction (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.purpose right.purpose) (fun _ => NativeBenefit.conjunction (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (fun _ => operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation)))) (1) ((partiesBudget left.consents right.consents+1+(1+1+(portsBudget left.gates right.gates+1+operationBudget left.operation right.operation)))) (party_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.signer right.signer) (pair_bound (parties (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.consents right.consents) (fun _ => NativeBenefit.conjunction (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.purpose right.purpose) (fun _ => NativeBenefit.conjunction (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (fun _ => operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation))) (partiesBudget left.consents right.consents) ((1+1+(portsBudget left.gates right.gates+1+operationBudget left.operation right.operation))) (parties_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.consents right.consents) (pair_bound (port (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.purpose right.purpose) (fun _ => NativeBenefit.conjunction (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (fun _ => operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation)) (1) ((portsBudget left.gates right.gates+1+operationBudget left.operation right.operation)) (port_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.purpose right.purpose) (pair_bound (ports (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (fun _ => operation (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation) (portsBudget left.gates right.gates) (operationBudget left.operation right.operation) (ports_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.gates right.gates) (operation_work_bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) left.operation right.operation)))))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.ActionWork
