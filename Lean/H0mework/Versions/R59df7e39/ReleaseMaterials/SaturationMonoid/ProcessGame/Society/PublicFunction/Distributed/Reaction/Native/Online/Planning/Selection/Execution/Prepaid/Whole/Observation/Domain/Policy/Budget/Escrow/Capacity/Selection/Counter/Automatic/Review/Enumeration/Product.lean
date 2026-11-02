import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Product
universe u v w
variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v} {Output : Type w}

/-- The continuation contains only choices already read from source fields. -/
inductive Task where
  | build (fields : List Key) (wrap : (∀ key ∈ fields,Value key) → Output)
  | alternatives (head : Key) (tail : List Key) (values : List (Value head))
      (wrap : (∀ key ∈ head::tail,Value key) → Output)
abbrev Queue := List (Task (Key := Key) (Value := Value) (Output := Output))
variable (choices : ∀ key,List (Value key))

def Task.denote : Task (Key := Key) (Value := Value) (Output := Output) → List Output
  | .build fields wrap => (List.pi fields choices).map wrap
  | .alternatives head tail values wrap => values.flatMap fun value =>
      (List.pi tail choices).map fun rest => wrap (List.Pi.cons head tail value rest)
def denote (queue : Queue (Key := Key) (Value := Value) (Output := Output)) := queue.flatMap (Task.denote choices)

inductive Event where
  | read (key : Key)
  | extend (key : Key) (value : Value key)
  | emit (value : Output)
  | close

def step : Queue (Key := Key) (Value := Value) (Output := Output) →
    Option (Queue (Key := Key) (Value := Value) (Output := Output) × Option Output × Event (Key := Key) (Value := Value) (Output := Output))
  | [] => none
  | .build [] wrap::rest => some (rest,some (wrap (List.Pi.nil Value)),.emit (wrap (List.Pi.nil Value)))
  | .build (head::tail) wrap::rest => some (.alternatives head tail (choices head) wrap::rest,none,.read head)
  | .alternatives _ _ [] _::rest => some (rest,none,.close)
  | .alternatives head tail (value::values) wrap::rest => some
      (.build tail (fun assignment => wrap (List.Pi.cons head tail value assignment))::
        .alternatives head tail values wrap::rest,none,.extend head value)

theorem one_step_conserves_order_and_multiplicity
    {before after : Queue (Key := Key) (Value := Value) (Output := Output)}
    {yielded : Option Output} {event : Event (Key := Key) (Value := Value) (Output := Output)}
    (observed : step choices before = some (after,yielded,event)) :
    denote choices before = yielded.toList++denote choices after := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | build fields wrap =>
      cases fields <;> dsimp only [step] at observed
      all_goals cases Option.some.inj observed
      all_goals simp [denote,Task.denote,List.pi,List.map_flatMap,List.map_map,Function.comp_def]
    | alternatives head tail values wrap =>
      cases values <;> dsimp only [step] at observed
      all_goals cases Option.some.inj observed
      all_goals simp [denote,Task.denote,List.append_assoc]

def cost : List Key → Nat
  | [] => 1
  | head::tail => 2+(choices head).length*(cost tail+1)
def cardinality : List Key → Nat
  | [] => 1
  | head::tail => (choices head).length*cardinality tail

theorem cardinality_is_the_source_product_size (fields : List Key) :
    (List.pi fields choices).length = cardinality choices fields := by
  induction fields with
  | nil => rfl
  | cons head tail ih => simp [List.pi,List.length_flatMap,ih,cardinality]

def Task.rank : Task (Key := Key) (Value := Value) (Output := Output) → Nat
  | .build fields _ => cost choices fields
  | .alternatives _ tail values _ => 1+values.length*(cost choices tail+1)
def rank (queue : Queue (Key := Key) (Value := Value) (Output := Output)) := (queue.map (Task.rank choices)).sum

theorem step_decreases_the_source_constructor_rank
    {before after : Queue (Key := Key) (Value := Value) (Output := Output)}
    {yielded : Option Output} {event : Event (Key := Key) (Value := Value) (Output := Output)}
    (observed : step choices before = some (after,yielded,event)) : rank choices after+1 = rank choices before := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | build fields wrap =>
      cases fields <;> dsimp only [step] at observed
      all_goals cases Option.some.inj observed
      all_goals simp only [rank,List.map_cons,List.sum_cons,Task.rank,cost]
      all_goals omega
    | alternatives head tail values wrap =>
      cases values with
      | nil =>
        dsimp only [step] at observed;cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,Nat.zero_mul,Nat.add_zero]
        omega
      | cons value values =>
        dsimp only [step] at observed;cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem stopped_iff_empty (queue : Queue (Key := Key) (Value := Value) (Output := Output)) : step choices queue = none ↔ queue = [] := by
  cases queue with
  | nil => simp [step]
  | cons task rest =>
    cases task with
    | build fields wrap => cases fields <;> simp [step]
    | alternatives head tail values wrap => cases values <;> simp [step]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Product
