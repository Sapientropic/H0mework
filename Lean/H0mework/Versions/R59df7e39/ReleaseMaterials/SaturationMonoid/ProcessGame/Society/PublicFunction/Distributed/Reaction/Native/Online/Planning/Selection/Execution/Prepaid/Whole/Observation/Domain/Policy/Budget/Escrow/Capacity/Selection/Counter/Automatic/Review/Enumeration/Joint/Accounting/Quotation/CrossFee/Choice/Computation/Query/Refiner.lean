import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Refiner
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol

namespace Generic
variable {Key α : Type} [DecidableEq Key]
variable (R : α → α → Prop) (pool : List α)
structure Evidence (current : Fin pool.length) (remaining : List (Fin pool.length)) (slot : Nat) : Prop where
  bounded : slot < pool.length
  no_worse : R (pool[slot]'bounded) pool[current]
  maximal : ∀ other ∈ remaining,¬ (R pool[other] (pool[slot]'bounded) ∧ ¬R (pool[slot]'bounded) pool[other])

variable (reflexive : ∀ item,R item item) (transitive : ∀ {a b c},R a b → R b c → R a c)
  (test : (previous candidate : α) → Code Key (.truth (R candidate previous ∧ ¬R previous candidate)))

def scan (current : Fin pool.length) : (remaining : List (Fin pool.length)) →
    Code Key (.number (Evidence R pool current remaining))
  | [] => .pure ⟨current.val,⟨current.isLt,reflexive _,by intro other inside;cases inside⟩⟩
  | head::tail => .bind (test pool[current] pool[head]) fun answer => match answer with
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

theorem Evidence.full_maximal {current : Fin pool.length} {slot : Nat}
    (evidence : Evidence R pool current (List.finRange pool.length) slot) :
    ∀ other ∈ pool,¬ (R other (pool[slot]'evidence.bounded) ∧ ¬R (pool[slot]'evidence.bounded) other) := by
  intro other inside
  obtain ⟨index,bounded,same⟩ := List.getElem_of_mem inside
  have stable := evidence.maximal ⟨index,bounded⟩ (List.mem_finRange _)
  change ¬ (R (pool[index]'bounded) (pool[slot]'evidence.bounded) ∧ ¬R (pool[slot]'evidence.bounded) (pool[index]'bounded)) at stable
  simpa only [same] using stable
end Generic

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
local notation "Program" => Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
variable (pool : List (Offer (prepared := prepared) (position := position)))

def Claim (ordinal : Nat) : Nat → Prop
  | 0 => pool.length ≤ ordinal
  | slot+1 => ∃ bounded : ordinal < pool.length,
      Generic.Evidence (ResponsibilityLe pool) pool ⟨ordinal,bounded⟩ (List.finRange pool.length) slot

-- Zero encodes a missing reference; a successor encodes the actual selected source ordinal.
def program (ordinal : Nat) : Program (.number (Claim pool ordinal)) :=
  .bind (.atom (.natural (ordinal+1) pool.length)) fun available => match available with
  | .isFalse absent => .pure ⟨0,by dsimp only [Claim];omega⟩
  | .isTrue enough =>
      let current : Fin pool.length := ⟨ordinal,by omega⟩
      .bind (Generic.scan (ResponsibilityLe pool) pool (responsibility_refl pool)
        (fun {a b c} => responsibility_trans pool (first := a) (middle := b) (last := c))
        (Source.strict pool) current (List.finRange pool.length)) fun selected =>
          .bind (.atom (.increment selected.val)) fun encoded =>
            .pure ⟨encoded.val,by rw [encoded.property];exact ⟨current.isLt,selected.property⟩⟩

variable {pool}
theorem evidence {ordinal slot : Nat} (yes : Claim pool ordinal (slot+1)) :
    Generic.Evidence (ResponsibilityLe pool) pool ⟨ordinal,yes.choose⟩ (List.finRange pool.length) slot := yes.choose_spec

theorem selected_is_member {ordinal slot : Nat} (yes : Claim pool ordinal (slot+1)) :
    (pool[slot]'(evidence yes).bounded) ∈ pool := List.getElem_mem _

theorem selected_is_independently_verified {ordinal slot : Nat} (yes : Claim pool ordinal (slot+1)) :
    Choice.verify pool (pool[ordinal]'yes.choose) (pool[slot]'(evidence yes).bounded) = true :=
  decide_eq_true ⟨(evidence yes).no_worse,(evidence yes).full_maximal _ _⟩

theorem every_available_improvement_is_selected {ordinal slot : Nat} (yes : Claim pool ordinal (slot+1))
    (available : ∃ other ∈ pool,ResponsibilityLe pool other (pool[ordinal]'yes.choose) ∧ ¬ResponsibilityLe pool (pool[ordinal]'yes.choose) other) :
    ResponsibilityLe pool (pool[slot]'(evidence yes).bounded) (pool[ordinal]'yes.choose) ∧
      ¬ResponsibilityLe pool (pool[ordinal]'yes.choose) (pool[slot]'(evidence yes).bounded) := by
  refine ⟨(evidence yes).no_worse,?_⟩
  intro backwards
  obtain ⟨other,inside,forward,strict⟩ := available
  exact (evidence yes).full_maximal _ _ other inside
    ⟨responsibility_trans pool forward backwards,fun reverse => strict (responsibility_trans pool backwards reverse)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Refiner
