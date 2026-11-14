import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeSuccessFinite

set_option autoImplicit false
namespace FlyCNS.C3NativeFinite
open C3FiniteOccurrence C3NativeMinimum

/-- The original guarded physical word bounds every successful autonomous
prefix. Source errors occur at an effect of one such prefix. -/
def prefixBound (boundary : Boundary) (anchor : Anchor boundary) : Nat :=
  256^(C3NativePrecision.width boundary anchor)/1000+3

theorem generated_index_bound {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {n : Nat} {current : Snapshot boundary} (paid : C3NativeMinimum.generate installed anchor n=.ok current) :
    n<prefixBound boundary anchor := by
  have visit:=C3NativeMinimum.generated_visit paid
  have bound:=C3NativePrecision.generated_visit_bound paid
  unfold C3NativePrecision.stateBound at bound
  unfold prefixBound
  omega

def letter (code : Fin 4) : Letter :=
  match code.val with
  | 0 => .inl ()
  | 1 => .inr .neural
  | 2 => .inr .damage
  | _ => .inr .repair

def letterCode : Letter → Fin 4
  | .inl _ => 0
  | .inr .neural => 1
  | .inr .damage => 2
  | .inr .repair => 3

theorem letter_roundtrip (input : Letter) : letter (letterCode input)=input := by
  cases input with
  | inl token => cases token;rfl
  | inr operation => cases operation <;> rfl

private theorem autonomous_effect {boundary : Boundary} (installed : Installed boundary) (state : Outcome boundary) :
    effect installed (.inl ()) state=state.bind (advance installed) := by
  cases state with
  | error why => rfl
  | ok current => simp only [effect,selected,ne_eq,not_true_eq_false,if_false,bind,Except.bind]

theorem execute_autonomous {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) (n : Nat) :
    execute installed (List.replicate n (.inl ())) (.ok anchor.base)=C3NativeMinimum.generate installed anchor n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    rw [List.replicate_add,execute_append,previous]
    simp only [List.replicate_succ,List.replicate_zero,C3NativeMinimum.execute]
    exact autonomous_effect installed _

private theorem error_first {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary)
    (word : List Letter) (n : Nat) (before : Snapshot boundary)
    (old : C3NativeMinimum.generate installed anchor n=.ok before) {why : String}
    (paid : execute installed word (.ok before)=.error why) :
    ∃ index : Fin (prefixBound boundary anchor),∃ input : Letter,
      effect installed input (C3NativeMinimum.generate installed anchor index.val)=.error why := by
  induction word generalizing n before with
  | nil => contradiction
  | cons input rest previous =>
    simp only [C3NativeMinimum.execute] at paid
    cases step:effect installed input (.ok before) with
    | error reason =>
      rw [step,C3NativeMinimum.execute_error] at paid
      have same:reason=why := Except.error.inj paid
      subst why
      refine ⟨⟨n,generated_index_bound old⟩,input,?_⟩
      rw [old]
      exact step
    | ok after =>
      rw [step] at paid
      have advancing:advance installed before=.ok after := by
        unfold effect at step
        simp only [bind,Except.bind] at step
        split at step
        · contradiction
        · exact step
      have generated:C3NativeMinimum.generate installed anchor (n+1)=.ok after := by
        simp only [C3NativeMinimum.generate,old,bind,Except.bind]
        exact advancing
      exact previous (n+1) after generated paid

abbrev Address (boundary : Boundary) (anchor : Anchor boundary) :=
  Fin (prefixBound boundary anchor) ⊕ (Fin (prefixBound boundary anchor) × Fin 4)

/-- An address generates its own autonomous prefix and optional first effect.
It carries no state table, error list or completed successor. -/
def fromAddress {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) :
    Address boundary anchor → Carrier boundary installed anchor
  | .inl index => fromWord boundary installed anchor (List.replicate index.val (.inl ()))
  | .inr (index,input) => fromWord boundary installed anchor
      (List.replicate index.val (.inl ())++[letter input])

theorem covers_carrier {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) :
    Function.Surjective (fromAddress installed anchor) := by
  intro state
  rcases state.property with ⟨word,paid⟩
  cases branch:state.val with
  | ok current =>
    rw [branch] at paid
    have generated:=success_is_autonomous paid
    refine ⟨.inl ⟨word.length,generated_index_bound generated⟩,?_⟩
    apply Subtype.ext
    change execute installed (List.replicate word.length (.inl ())) (.ok anchor.base)=state.val
    rw [execute_autonomous,generated]
    exact branch.symm
  | error why =>
    rw [branch] at paid
    rcases error_first installed anchor word 0 anchor.base rfl paid with ⟨index,input,first⟩
    refine ⟨.inr (index,letterCode input),?_⟩
    apply Subtype.ext
    change execute installed (List.replicate index.val (.inl ())++[letter (letterCode input)])
      (.ok anchor.base)=state.val
    rw [execute_append,execute_autonomous,letter_roundtrip]
    simp only [C3NativeMinimum.execute]
    exact first.trans branch.symm

theorem finite_carrier (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (Carrier boundary installed anchor) :=
  Finite.of_surjective (fromAddress installed anchor) (covers_carrier installed anchor)

theorem finite_original_key (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (C3NativeMinimum.Encoded boundary installed anchor) := by
  have := finite_carrier boundary installed anchor
  apply Finite.of_injective (C3NativeMinimum.unpack (boundary:=boundary) (installed:=installed) (anchor:=anchor))
  intro left right equal
  have packed:=congrArg C3NativeMinimum.pack equal
  simpa only [C3NativeMinimum.pack_unpack] using packed

theorem finite_precision_key (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (C3NativePrecision.Encoded boundary installed anchor) := by
  have := finite_carrier boundary installed anchor
  apply Finite.of_injective (C3NativePrecision.unpack (boundary:=boundary) (installed:=installed) (anchor:=anchor))
  intro left right equal
  have packed:=congrArg C3NativePrecision.pack equal
  simpa only [C3NativePrecision.pack_unpack] using packed

end FlyCNS.C3NativeFinite
