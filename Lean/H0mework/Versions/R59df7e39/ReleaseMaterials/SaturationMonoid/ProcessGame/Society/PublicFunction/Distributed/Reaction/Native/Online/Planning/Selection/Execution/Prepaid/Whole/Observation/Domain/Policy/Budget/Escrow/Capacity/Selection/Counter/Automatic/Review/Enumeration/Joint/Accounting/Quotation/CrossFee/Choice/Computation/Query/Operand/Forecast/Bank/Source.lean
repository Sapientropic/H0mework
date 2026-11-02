import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
  {pool : List (Offer (prepared := prepared) (position := position))}
  {tables : Tables.Completed pool} (cache : Completed tables)
local notation "Program" => Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))

namespace Cached

def TensorRows (new previous : Fin pool.length) : Prop :=
  ∀ index ∈ keys prepared,∀ table ∈ List.finRange (tables.at index).length,
    Full.TensorLe (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous)
def CostRows (new previous : Fin pool.length) : Prop :=
  (∀ index ∈ keys prepared,(pool[new]).work index ≤ (pool[previous]).work index ∧ (pool[previous]).credit index ≤ (pool[new]).credit index) ∧
  (pool[new]).branch.alternative.1 ≤ (pool[previous]).branch.alternative.1 ∧
    (pool[new]).invoiceWork ≤ (pool[previous]).invoiceWork ∧ (pool[previous]).invoiceCredit ≤ (pool[new]).invoiceCredit

theorem rows_iff (new previous : Fin pool.length) : TensorRows cache new previous ∧ CostRows new previous ↔ ResponsibilityLe pool pool[new] pool[previous] := by
  constructor
  · rintro ⟨tensors,costs,invoices⟩
    refine ⟨?_,fun index => costs index (List.mem_finRange _),invoices⟩
    intro index table member
    have sameTables : tables.at index = Choice.tables pool index := tables.at_exact index
    rw [←sameTables] at member
    obtain ⟨ordinal,bounded,same⟩ := List.getElem_of_mem member
    have checked := tensors index (List.mem_finRange _) ⟨ordinal,bounded⟩ (List.mem_finRange _)
    simp only [Completed.tensor_exact] at checked
    change Full.TensorLe (Policy.initial input prepared.saved[index].point)
      (((pool[new]).view index).tensor (Choice.rival pool index ((tables.at index)[ordinal]'bounded)))
      (((pool[previous]).view index).tensor (Choice.rival pool index ((tables.at index)[ordinal]'bounded))) at checked
    rw [same] at checked
    exact checked
  · intro valid
    refine ⟨?_,fun index _ => valid.2.1 index,valid.2.2⟩
    intro index _ table _
    rw [Completed.tensor_exact,Completed.tensor_exact]
    apply valid.1 index
    have sameTables : tables.at index = Choice.tables pool index := tables.at_exact index
    rw [←sameTables];exact List.getElem_mem _

def responsibility (new previous : Fin pool.length) : Program (.truth (ResponsibilityLe pool pool[new] pool[previous])) :=
  let tensors : Program (.truth (TensorRows cache new previous)) :=
    Query.Source.Generic.rows (fun index => ∀ table ∈ List.finRange (tables.at index).length,
      Full.TensorLe (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous))
      (fun index => Query.Source.Generic.rows
        (fun table => Full.TensorLe (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous))
        (fun table => Query.Source.tensor (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous))
        (List.finRange (tables.at index).length)) (keys prepared)
  let costs : Program (.truth (∀ index ∈ keys prepared,(pool[new]).work index ≤ (pool[previous]).work index ∧ (pool[previous]).credit index ≤ (pool[new]).credit index)) :=
    Query.Source.Generic.rows _ (fun index : Index prepared =>
      Code.conjunction (.atom (.natural ((pool[new]).work index) ((pool[previous]).work index)))
        (fun _ => .atom (.natural ((pool[previous]).credit index) ((pool[new]).credit index)))) (keys prepared)
  let invoices : Program (.truth ((pool[new]).branch.alternative.1 ≤ (pool[previous]).branch.alternative.1 ∧
      (pool[new]).invoiceWork ≤ (pool[previous]).invoiceWork ∧ (pool[previous]).invoiceCredit ≤ (pool[new]).invoiceCredit)) :=
    Code.conjunction (.atom (.natural (pool[new]).branch.alternative.1 (pool[previous]).branch.alternative.1)) (fun _ =>
      Code.conjunction (.atom (.natural (pool[new]).invoiceWork (pool[previous]).invoiceWork)) (fun _ =>
        .atom (.natural (pool[previous]).invoiceCredit (pool[new]).invoiceCredit)))
  Code.transport (rows_iff cache new previous) (Code.conjunction tensors (fun _ => Code.conjunction costs (fun _ => invoices)))

def strict (previous new : Fin pool.length) : Program (.truth (ResponsibilityLe pool pool[new] pool[previous] ∧ ¬ResponsibilityLe pool pool[previous] pool[new])) :=
  Code.conjunction (responsibility cache new previous) (fun _ => Code.negative (responsibility cache previous new))

def responsibilityShape (new previous : Fin pool.length) :=
  let tensors := CapacityBound.rows (fun index => CapacityBound.rows (fun table =>
    CapacityBound.Shapes.tensor (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous))
    (List.finRange (tables.at index).length)) (keys prepared)
  let costs := CapacityBound.rows (fun _ : Index prepared => CapacityBound.pair 2 2) (keys prepared)
  CapacityBound.lift (CapacityBound.pair tensors (CapacityBound.pair costs (CapacityBound.pair 2 (CapacityBound.pair 2 2))))

theorem responsibility_bound (new previous : Fin pool.length) : (responsibility cache new previous).cost ≤ responsibilityShape cache new previous := by
  unfold responsibility responsibilityShape
  apply CapacityBound.transport_bound
  apply CapacityBound.conjunction_bound
  · exact CapacityBound.rows_bound _ _ _ (fun index => CapacityBound.rows_bound _ _ _ (fun table => CapacityBound.Shapes.tensor_bound _ _ _) _) _
  apply CapacityBound.conjunction_bound
  · exact CapacityBound.rows_bound _ _ _ (fun _ => CapacityBound.conjunction_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2)) _
  exact CapacityBound.conjunction_bound _ _ (Nat.le_refl 2) (CapacityBound.conjunction_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2))

def strictShape (previous new : Fin pool.length) := CapacityBound.pair (responsibilityShape cache new previous) (CapacityBound.lift (responsibilityShape cache previous new))
theorem strict_bound (previous new : Fin pool.length) : (strict cache previous new).cost ≤ strictShape cache previous new :=
  CapacityBound.conjunction_bound _ _ (responsibility_bound cache new previous) (CapacityBound.negative_bound _ (responsibility_bound cache previous new))

def responsibilityBudget (new previous : Fin pool.length) : Meter.Number (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (responsibilityShape cache new previous) := by
  unfold responsibilityShape
  apply Meter.lift;apply Meter.pair
  · apply Meter.rows;intro index
    apply Meter.rows;intro table
    exact Meter.Compiler.tensor (Policy.initial input prepared.saved[index].point) (cache.tensor index table new) (cache.tensor index table previous)
  intro _;apply Meter.pair
  · exact Meter.rows (fun _ : Index prepared => Meter.pair (Meter.literal 2) (fun _ => Meter.literal 2)) (keys prepared)
  intro _;exact Meter.pair (Meter.literal 2) (fun _ => Meter.pair (Meter.literal 2) (fun _ => Meter.literal 2))
def strictBudget (previous new : Fin pool.length) : Meter.Number (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (strictShape cache previous new) :=
  Meter.pair (responsibilityBudget cache new previous) (fun _ => Meter.lift (responsibilityBudget cache previous new))
end Cached

namespace FinScan
variable {Key α : Type} [DecidableEq Key] (R : α → α → Prop) (pool : List α)
  (reflexive : ∀ item,R item item) (transitive : ∀ {a b c},R a b → R b c → R a c)
  (test : (previous candidate : Fin pool.length) → Code Key (.truth (R pool[candidate] pool[previous] ∧ ¬R pool[previous] pool[candidate])))
def scan (current : Fin pool.length) : (remaining : List (Fin pool.length)) →
    Code Key (.number (Query.Refiner.Generic.Evidence R pool current remaining))
  | [] => .pure ⟨current.val,⟨current.isLt,reflexive _,by intro other inside;cases inside⟩⟩
  | head::tail => .bind (test current head) fun answer => match answer with
    | .isTrue better => .bind (scan head tail) fun later =>
        .pure ⟨later.val,⟨later.property.bounded,transitive later.property.no_worse better.1,by
          intro other inside
          rcases List.mem_cons.mp inside with same | rest
          · subst other;exact fun backwards => backwards.2 later.property.no_worse
          · exact later.property.maximal other rest⟩⟩
    | .isFalse notBetter => .bind (scan current tail) fun later =>
        .pure ⟨later.val,⟨later.property.bounded,later.property.no_worse,by
          intro other inside
          rcases List.mem_cons.mp inside with same | rest
          · subst other;intro backwards
            exact notBetter ⟨transitive backwards.1 later.property.no_worse,
              fun reverse => backwards.2 (transitive later.property.no_worse reverse)⟩
          · exact later.property.maximal other rest⟩⟩

variable (limit : Nat) (within : ∀ left right,(test left right).cost ≤ limit)
include within
theorem scan_bound (current : Fin pool.length) (remaining : List (Fin pool.length)) :
    (scan R pool reflexive transitive test current remaining).cost ≤ 1+remaining.length*(limit+3) := by
  induction remaining generalizing current with
  | nil => simp [scan,Code.cost]
  | cons head tail ih =>
      apply Nat.le_trans (CapacityBound.bind_bound _ _ (within current head) (b := 1+tail.length*(limit+3)+2) ?_)
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
      intro answer;cases answer with
      | isFalse notBetter =>
          apply Nat.le_trans (CapacityBound.bind_bound _ _ (ih current) (b := 1) ?_)
          · omega
          intro later;exact Nat.le_refl 1
      | isTrue better =>
          apply Nat.le_trans (CapacityBound.bind_bound _ _ (ih head) (b := 1) ?_)
          · omega
          intro later;exact Nat.le_refl 1
end FinScan

namespace Cached
def program (ordinal : Nat) : Program (.number (Query.Refiner.Claim pool ordinal)) :=
  .bind (.atom (.natural (ordinal+1) pool.length)) fun available => match available with
  | .isFalse absent => .pure ⟨0,by dsimp only [Query.Refiner.Claim];omega⟩
  | .isTrue enough =>
      let current : Fin pool.length := ⟨ordinal,by omega⟩
      .bind (FinScan.scan (ResponsibilityLe pool) pool (responsibility_refl pool)
        (fun {a b c} => responsibility_trans pool (first := a) (middle := b) (last := c)) (strict cache) current (List.finRange pool.length)) fun selected =>
          .bind (.atom (.increment selected.val)) fun encoded =>
            .pure ⟨encoded.val,by rw [encoded.property];exact ⟨current.isLt,selected.property⟩⟩

def maximum := ((List.finRange pool.length).flatMap fun previous => (List.finRange pool.length).map (strictShape cache previous)).foldr Nat.max 0
private theorem member_le_max {value : Nat} {values : List Nat} (inside : value ∈ values) : value ≤ values.foldr Nat.max 0 := by
  induction values with
  | nil => cases inside
  | cons head tail ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst value;exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

theorem maximum_covers (left right : Fin pool.length) : (strict cache left right).cost ≤ maximum cache :=
  (strict_bound cache left right).trans (member_le_max (List.mem_flatMap.mpr
    ⟨left,List.mem_finRange _,List.mem_map.mpr ⟨right,List.mem_finRange _,rfl⟩⟩))
def budget := 9+pool.length*(maximum cache+3)

theorem program_bound (ordinal : Nat) : (program cache ordinal).cost ≤ budget cache := by
  unfold program
  have first : (Code.atom (.natural (ordinal+1) pool.length) : Code
      (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (.truth (ordinal+1 ≤ pool.length))).cost ≤ 2 := Nat.le_refl 2
  apply Nat.le_trans (CapacityBound.bind_bound _ _ first (b := 1+pool.length*(maximum cache+3)+5) ?_)
  · dsimp only [budget];omega
  intro answer;cases answer with
  | isFalse absent => change 1 ≤ _;omega
  | isTrue enough =>
      apply Nat.le_trans (CapacityBound.bind_bound _ _
        (FinScan.scan_bound (ResponsibilityLe pool) pool (responsibility_refl pool)
          (fun {a b c} => responsibility_trans pool (first := a) (middle := b) (last := c))
          (strict cache) (maximum cache) (maximum_covers cache) _ (List.finRange pool.length)) (b := 4) ?_)
      · rw [List.length_finRange];omega
      intro selected
      refine CapacityBound.bind_bound _ _ (a := 2) (b := 1) ?_ ?_
      · exact Nat.le_refl 2
      intro encoded;exact Nat.le_refl 1

theorem initial_rank_bound (ordinal : Nat) : (Query.initial (program cache ordinal)).rank ≤ budget cache := by
  simpa only [Query.initial,State.rank,Phase.rank,Kont.cost,Nat.add_zero] using program_bound cache ordinal

def quote : Meter.Number (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (budget cache) :=
  .bind (Meter.length pool) fun count =>
    .bind (Meter.maxPairs (budget := strictShape cache) (strictBudget cache) (List.finRange pool.length) (List.finRange pool.length)) fun largest =>
      .bind (Meter.add largest.val 3) fun padded => .bind (Meter.multiply count.val padded.val) fun product =>
        .bind (Meter.add product.val 9) fun answer => .pure ⟨answer.val,by
          rw [answer.property,product.property,padded.property,count.property,largest.property]
          exact Nat.add_comm _ _⟩
end Cached
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank
