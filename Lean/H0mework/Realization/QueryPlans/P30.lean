/-
  Proposition 30: Kleisli completeness for generative atom-field queries.

  Proposition 25 proved completeness for the safe atom-field `image` fragment:
  follow one explicit field relation from a materialized query result.  This
  file lifts the same idea to the natural "query = generation" algebra:

    run a query, then for each produced row run a source-indexed continuation.

  Algebraically this is the powerset/Kleisli bind.  Logically it is exactly a
  range-restricted existential binder.  This is the closed mathematical core for
  multi-step generative query plans: score fusion, authority gates, gluing
  probes, and other runtime generators may enter as named predicates/relations,
  but generation itself is represented by `bind`.

  Boundary: the theorem is complete for this typed syntax.  It does not claim
  that every external-model proposal, source reopen, or runtime candidate
  generator has been faithfully represented by a primitive predicate/relation.
-/

import H0mework.Realization.QuerySupport.P25

/-! ## Kleisli / generative atom-field algebra -/

/-- Generative atom-field algebra over a fixed row type.  `bind q k` means:
    first evaluate `q`; for each source row produced by `q`, evaluate `k source`.
    This is the powerset-monad form of query-as-generation. -/
inductive KleisliFieldAlg (Row Base : Type*) where
  | empty
  | top
  | base : Base -> KleisliFieldAlg Row Base
  | union : KleisliFieldAlg Row Base -> KleisliFieldAlg Row Base ->
      KleisliFieldAlg Row Base
  | inter : KleisliFieldAlg Row Base -> KleisliFieldAlg Row Base ->
      KleisliFieldAlg Row Base
  | diff : KleisliFieldAlg Row Base -> KleisliFieldAlg Row Base ->
      KleisliFieldAlg Row Base
  | select : (Row -> Prop) -> KleisliFieldAlg Row Base ->
      KleisliFieldAlg Row Base
  | bind : KleisliFieldAlg Row Base -> (Row -> KleisliFieldAlg Row Base) ->
      KleisliFieldAlg Row Base

namespace KleisliFieldAlg

/-- Denotation of the generative algebra. -/
def eval {Row Base : Type*} (env : Base -> Row -> Prop) :
    KleisliFieldAlg Row Base -> Row -> Prop
  | empty, _row => False
  | top, _row => True
  | base b, row => env b row
  | union p q, row => eval env p row \/ eval env q row
  | inter p q, row => eval env p row /\ eval env q row
  | diff p q, row => eval env p row /\ ¬ eval env q row
  | select predicate q, row => predicate row /\ eval env q row
  | bind q k, row => exists source, eval env q source /\ eval env (k source) row

/-- The usual one-step field image is a special case of Kleisli bind. -/
def image {Row Base : Type*} (relation : Row -> Row -> Prop)
    (q : KleisliFieldAlg Row Base) : KleisliFieldAlg Row Base :=
  bind q (fun source => select (fun target => relation source target) top)

/-- Kleisli image has exactly the expected existential traversal semantics. -/
theorem image_eval {Row Base : Type*} (env : Base -> Row -> Prop)
    (relation : Row -> Row -> Prop) (q : KleisliFieldAlg Row Base)
    (target : Row) :
    eval env (image relation q) target <->
      exists source, eval env q source /\ relation source target := by
  simp [image, eval]

/-- A named runtime generator is just an indexed field relation. -/
def namedImage {Row Base Gen : Type*} (genRel : Gen -> Row -> Row -> Prop)
    (generator : Gen) (q : KleisliFieldAlg Row Base) :
    KleisliFieldAlg Row Base :=
  image (genRel generator) q

/-- Named generator semantics is still ordinary existential traversal. -/
theorem namedImage_eval {Row Base Gen : Type*}
    (env : Base -> Row -> Prop) (genRel : Gen -> Row -> Row -> Prop)
    (generator : Gen) (q : KleisliFieldAlg Row Base) (target : Row) :
    eval env (namedImage genRel generator q) target <->
      exists source, eval env q source /\ genRel generator source target := by
  simp [namedImage, image, eval]

end KleisliFieldAlg

/-! ## Range-restricted generative calculus -/

/-- Safe calculus matching the Kleisli algebra.  `bindExists f k` is a
    range-restricted existential: only rows satisfying `f` may seed the
    continuation `k`. -/
inductive KleisliFieldCalc (Row Base : Type*) where
  | falsity
  | truth
  | base : Base -> KleisliFieldCalc Row Base
  | pred : (Row -> Prop) -> KleisliFieldCalc Row Base
  | not : KleisliFieldCalc Row Base -> KleisliFieldCalc Row Base
  | and : KleisliFieldCalc Row Base -> KleisliFieldCalc Row Base ->
      KleisliFieldCalc Row Base
  | or : KleisliFieldCalc Row Base -> KleisliFieldCalc Row Base ->
      KleisliFieldCalc Row Base
  | bindExists : KleisliFieldCalc Row Base ->
      (Row -> KleisliFieldCalc Row Base) -> KleisliFieldCalc Row Base

namespace KleisliFieldCalc

/-- Denotation of the range-restricted generative calculus. -/
def eval {Row Base : Type*} (env : Base -> Row -> Prop) :
    KleisliFieldCalc Row Base -> Row -> Prop
  | falsity, _row => False
  | truth, _row => True
  | base b, row => env b row
  | pred predicate, row => predicate row
  | not f, row => ¬ eval env f row
  | and p q, row => eval env p row /\ eval env q row
  | or p q, row => eval env p row \/ eval env q row
  | bindExists f k, row =>
      exists source, eval env f source /\ eval env (k source) row

end KleisliFieldCalc

/-! ## Denotation-preserving translations -/

/-- Compile generative algebra to range-restricted calculus. -/
def kleisliAlgToCalc {Row Base : Type*} :
    KleisliFieldAlg Row Base -> KleisliFieldCalc Row Base
  | KleisliFieldAlg.empty => KleisliFieldCalc.falsity
  | KleisliFieldAlg.top => KleisliFieldCalc.truth
  | KleisliFieldAlg.base b => KleisliFieldCalc.base b
  | KleisliFieldAlg.union p q =>
      KleisliFieldCalc.or (kleisliAlgToCalc p) (kleisliAlgToCalc q)
  | KleisliFieldAlg.inter p q =>
      KleisliFieldCalc.and (kleisliAlgToCalc p) (kleisliAlgToCalc q)
  | KleisliFieldAlg.diff p q =>
      KleisliFieldCalc.and (kleisliAlgToCalc p)
        (KleisliFieldCalc.not (kleisliAlgToCalc q))
  | KleisliFieldAlg.select predicate q =>
      KleisliFieldCalc.and (KleisliFieldCalc.pred predicate)
        (kleisliAlgToCalc q)
  | KleisliFieldAlg.bind q k =>
      KleisliFieldCalc.bindExists (kleisliAlgToCalc q)
        (fun source => kleisliAlgToCalc (k source))

/-- Compile range-restricted calculus back to generative algebra. -/
def kleisliCalcToAlg {Row Base : Type*} :
    KleisliFieldCalc Row Base -> KleisliFieldAlg Row Base
  | KleisliFieldCalc.falsity => KleisliFieldAlg.empty
  | KleisliFieldCalc.truth => KleisliFieldAlg.top
  | KleisliFieldCalc.base b => KleisliFieldAlg.base b
  | KleisliFieldCalc.pred predicate =>
      KleisliFieldAlg.select predicate KleisliFieldAlg.top
  | KleisliFieldCalc.not f =>
      KleisliFieldAlg.diff KleisliFieldAlg.top (kleisliCalcToAlg f)
  | KleisliFieldCalc.and p q =>
      KleisliFieldAlg.inter (kleisliCalcToAlg p) (kleisliCalcToAlg q)
  | KleisliFieldCalc.or p q =>
      KleisliFieldAlg.union (kleisliCalcToAlg p) (kleisliCalcToAlg q)
  | KleisliFieldCalc.bindExists f k =>
      KleisliFieldAlg.bind (kleisliCalcToAlg f)
        (fun source => kleisliCalcToAlg (k source))

/-- THEOREM 1: algebra-to-calculus compilation preserves denotation. -/
theorem kleisliAlgToCalc_sound {Row Base : Type*}
    (env : Base -> Row -> Prop) :
    forall q row, KleisliFieldCalc.eval env (kleisliAlgToCalc q) row <->
      KleisliFieldAlg.eval env q row := by
  intro q
  induction q with
  | empty =>
      intro row
      rfl
  | top =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | union p q ihp ihq =>
      intro row
      simp [kleisliAlgToCalc, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [kleisliAlgToCalc, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [kleisliAlgToCalc, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [kleisliAlgToCalc, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ih row]
  | bind q k ihq ihk =>
      intro row
      simp [kleisliAlgToCalc, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihq, ihk]

/-- THEOREM 2: calculus-to-algebra compilation preserves denotation. -/
theorem kleisliCalcToAlg_sound {Row Base : Type*}
    (env : Base -> Row -> Prop) :
    forall f row, KleisliFieldAlg.eval env (kleisliCalcToAlg f) row <->
      KleisliFieldCalc.eval env f row := by
  intro f
  induction f with
  | falsity =>
      intro row
      rfl
  | truth =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | pred predicate =>
      intro row
      simp [kleisliCalcToAlg, KleisliFieldAlg.eval, KleisliFieldCalc.eval]
  | not f ih =>
      intro row
      simp [kleisliCalcToAlg, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ih row]
  | and p q ihp ihq =>
      intro row
      simp [kleisliCalcToAlg, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihp row, ihq row]
  | or p q ihp ihq =>
      intro row
      simp [kleisliCalcToAlg, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihp row, ihq row]
  | bindExists f k ihf ihk =>
      intro row
      simp [kleisliCalcToAlg, KleisliFieldAlg.eval, KleisliFieldCalc.eval,
        ihf, ihk]

/-- THEOREM 3: every generative algebra query has an equivalent
    range-restricted calculus formula. -/
theorem kleisliAlg_expressible_by_calc {Row Base : Type*}
    (env : Base -> Row -> Prop) (q : KleisliFieldAlg Row Base) :
    exists f, forall row, KleisliFieldCalc.eval env f row <->
      KleisliFieldAlg.eval env q row := by
  exact ⟨kleisliAlgToCalc q, kleisliAlgToCalc_sound env q⟩

/-- THEOREM 4: every range-restricted calculus formula has an equivalent
    generative algebra query. -/
theorem kleisliCalc_expressible_by_alg {Row Base : Type*}
    (env : Base -> Row -> Prop) (f : KleisliFieldCalc Row Base) :
    exists q, forall row, KleisliFieldAlg.eval env q row <->
      KleisliFieldCalc.eval env f row := by
  exact ⟨kleisliCalcToAlg f, kleisliCalcToAlg_sound env f⟩

/-! ## Compatibility with Proposition 25's image fragment -/

/-- Embed the Proposition 25 safe atom-field algebra into the Kleisli algebra. -/
def fieldRelAlgToKleisli {Row Base : Type*} :
    FieldRelAlg Row Base -> KleisliFieldAlg Row Base
  | FieldRelAlg.empty => KleisliFieldAlg.empty
  | FieldRelAlg.top => KleisliFieldAlg.top
  | FieldRelAlg.base b => KleisliFieldAlg.base b
  | FieldRelAlg.union p q =>
      KleisliFieldAlg.union (fieldRelAlgToKleisli p) (fieldRelAlgToKleisli q)
  | FieldRelAlg.inter p q =>
      KleisliFieldAlg.inter (fieldRelAlgToKleisli p) (fieldRelAlgToKleisli q)
  | FieldRelAlg.diff p q =>
      KleisliFieldAlg.diff (fieldRelAlgToKleisli p) (fieldRelAlgToKleisli q)
  | FieldRelAlg.select predicate q =>
      KleisliFieldAlg.select predicate (fieldRelAlgToKleisli q)
  | FieldRelAlg.image relation q =>
      KleisliFieldAlg.image relation (fieldRelAlgToKleisli q)

/-- THEOREM 5: the old `image` fragment embeds denotation-preservingly into
    the Kleisli/generative algebra. -/
theorem fieldRelAlgToKleisli_sound {Row Base : Type*}
    (env : Base -> Row -> Prop) :
    forall q row, KleisliFieldAlg.eval env (fieldRelAlgToKleisli q) row <->
      FieldRelAlg.eval env q row := by
  intro q
  induction q with
  | empty =>
      intro row
      rfl
  | top =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | union p q ihp ihq =>
      intro row
      simp [fieldRelAlgToKleisli, KleisliFieldAlg.eval, FieldRelAlg.eval,
        ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [fieldRelAlgToKleisli, KleisliFieldAlg.eval, FieldRelAlg.eval,
        ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [fieldRelAlgToKleisli, KleisliFieldAlg.eval, FieldRelAlg.eval,
        ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [fieldRelAlgToKleisli, KleisliFieldAlg.eval, FieldRelAlg.eval,
        ih row]
  | image relation q ih =>
      intro row
      simp [fieldRelAlgToKleisli, KleisliFieldAlg.image,
        KleisliFieldAlg.eval, FieldRelAlg.eval, ih]

/-!
  Summary:
  - `KleisliFieldAlg` is the multi-step generative atom-field query algebra.
  - `KleisliFieldCalc` is the matching range-restricted existential calculus.
  - The translations are mutually denotation-preserving.
  - Proposition 25's one-step `image` algebra embeds into this Kleisli algebra.

  Remaining boundary:
  - A runtime generator must still be represented as a declared primitive
    predicate/relation before this theorem applies.  The theorem says the
    resulting generative query language is complete relative to those
    primitives, not that every model-generated candidate is automatically
    source-backed or cheap.
-/
