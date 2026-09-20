import H0mework.Arithmetic.PrimeShadow.P546

/-!
# Proposition 547: every σ-relaxed object has the standard object as its zero fiber

P537 proved the module-valued algebraic law

`relaxModule target 0 x = x`.

The user's stronger formulation is object-level rather than pointwise:
for an arbitrary standard object `X`, its σ-relaxed rewrite `X_σ` is `X`
decorated by a headroom/saturation coordinate, and at `σ = 0` that headroom
must be irrelevant.  A raw product `X × H` is not isomorphic to `X`; the
correct zero-fiber is therefore the quotient that identifies all headroom
choices above the same base point.

This file proves the generic theorem:

* define `X_σ` as a quotient of `X × H`;
* define the forgetful map `π : X_0 -> X`;
* prove `π` is an equivalence at `σ = 0`;
* prove unary/binary/predicate structure is pushed forward to the standard
  structure on `X`;
* equip `X_0` with the induced topology and obtain a homeomorphism to `X`.

Thus standard mathematics is literally the zero fiber of the saturated /
relaxed mathematics construction, not a separate parallel copy.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## The σ-relaxed quotient -/

/-- Raw σ-relaxed data: a base object plus a headroom/saturation decoration. -/
abbrev SigmaRelaxedRaw (X : Type v) (H : Type w) : Type (max v w) :=
  X × H

/-- The σ-relaxation relation.  At the annealing point `σ = 0`, all headroom
values over the same base point are identified.  Away from zero, this relation
keeps only literal equality.

The active branch is included so the same relation has the intended
nonzero-fiber shape, but the theorems below need only the zero fiber. -/
inductive SigmaRelaxationRel
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (σ : K) : SigmaRelaxedRaw X H -> SigmaRelaxedRaw X H -> Prop
  | zero {a b : SigmaRelaxedRaw X H}
      (hσ : σ = 0) (hbase : a.1 = b.1) :
      SigmaRelaxationRel σ a b
  | active {a b : SigmaRelaxedRaw X H}
      (hσ : σ ≠ 0) (heq : a = b) :
      SigmaRelaxationRel σ a b

/-- The σ-relaxed object `X_σ`: a quotient of `X` decorated with headroom. -/
abbrev SigmaRelaxedObject
    (K : Type u) [Zero K] (X : Type v) (H : Type w) (σ : K) :
    Type (max v w) :=
  Quot (SigmaRelaxationRel (K := K) (X := X) (H := H) σ)

/-- Build a σ-relaxed point from a base point and a headroom decoration. -/
def sigmaRelaxedMk
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (σ : K) (x : X) (h : H) : SigmaRelaxedObject K X H σ :=
  Quot.mk (SigmaRelaxationRel (K := K) (X := X) (H := H) σ) (x, h)

/-- THEOREM 1: at `σ = 0`, the headroom coordinate is irrelevant. -/
theorem sigmaZero_headroom_irrelevant
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (x : X) (h₁ h₂ : H) :
    sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₁ =
      sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₂ := by
  exact Quot.sound (SigmaRelaxationRel.zero (σ := (0 : K)) rfl rfl)

/-! ## The zero-fiber forgetful equivalence -/

/-- Forget the headroom coordinate at the zero fiber. -/
def sigmaZeroForget
    {K : Type u} [Zero K] {X : Type v} {H : Type w} :
    SigmaRelaxedObject K X H (0 : K) -> X :=
  Quot.lift Prod.fst (by
    intro a b h
    cases h with
    | zero hσ hbase =>
        exact hbase
    | active hσ heq =>
        exact False.elim (hσ rfl))

/-- Embed a standard point into the zero fiber using an arbitrary default
headroom.  The previous theorem proves that the choice is irrelevant. -/
def sigmaZeroEmbed
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (x : X) : SigmaRelaxedObject K X H (0 : K) :=
  sigmaRelaxedMk (K := K) (σ := (0 : K)) x default

@[simp] theorem sigmaZeroForget_embed
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (x : X) :
    sigmaZeroForget (K := K) (X := X) (H := H)
        (sigmaZeroEmbed (K := K) (X := X) (H := H) x) = x :=
  rfl

@[simp] theorem sigmaZeroEmbed_forget
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    sigmaZeroEmbed (K := K) (X := X) (H := H)
        (sigmaZeroForget (K := K) (X := X) (H := H) z) = z := by
  refine Quot.inductionOn z ?_
  intro a
  rcases a with ⟨x, h⟩
  exact sigmaZero_headroom_irrelevant (K := K) x default h

/-- THEOREM 2: `X_0` is canonically equivalent to the standard object `X`. -/
def sigmaZeroRelaxedEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w) [Inhabited H] :
    SigmaRelaxedObject K X H (0 : K) ≃ X where
  toFun := sigmaZeroForget (K := K) (X := X) (H := H)
  invFun := sigmaZeroEmbed (K := K) (X := X) (H := H)
  left_inv := sigmaZeroEmbed_forget (K := K) (X := X) (H := H)
  right_inv := sigmaZeroForget_embed (K := K) (X := X) (H := H)

/-! ## Push-forward of algebraic and logical structure -/

/-- Lift a unary operation on `X` to the zero fiber by transporting through the
forgetful equivalence. -/
def sigmaZeroLiftUnary
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (f : X -> X) :
    SigmaRelaxedObject K X H (0 : K) ->
      SigmaRelaxedObject K X H (0 : K) :=
  fun z => sigmaZeroEmbed (K := K) (X := X) (H := H)
    (f (sigmaZeroForget (K := K) (X := X) (H := H) z))

/-- THEOREM 3: unary operations push forward to the original operation on
`X`. -/
@[simp] theorem sigmaZeroForget_liftUnary
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (f : X -> X) (z : SigmaRelaxedObject K X H (0 : K)) :
    sigmaZeroForget (K := K) (X := X) (H := H)
        (sigmaZeroLiftUnary (K := K) (H := H) f z) =
      f (sigmaZeroForget (K := K) (X := X) (H := H) z) :=
  rfl

/-- Lift a binary operation on `X` to the zero fiber. -/
def sigmaZeroLiftBinary
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X) :
    SigmaRelaxedObject K X H (0 : K) ->
      SigmaRelaxedObject K X H (0 : K) ->
        SigmaRelaxedObject K X H (0 : K) :=
  fun a b => sigmaZeroEmbed (K := K) (X := X) (H := H)
    (op
      (sigmaZeroForget (K := K) (X := X) (H := H) a)
      (sigmaZeroForget (K := K) (X := X) (H := H) b))

/-- THEOREM 4: binary operations push forward to the original operation on
`X`. -/
@[simp] theorem sigmaZeroForget_liftBinary
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X)
    (a b : SigmaRelaxedObject K X H (0 : K)) :
    sigmaZeroForget (K := K) (X := X) (H := H)
        (sigmaZeroLiftBinary (K := K) (H := H) op a b) =
      op
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
        (sigmaZeroForget (K := K) (X := X) (H := H) b) :=
  rfl

/-- THEOREM 5: associativity transfers from `X` to the zero fiber. -/
theorem sigmaZeroLiftBinary_assoc_of_assoc
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X)
    (hassoc : ∀ x y z : X, op (op x y) z = op x (op y z)) :
    ∀ a b c : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroLiftBinary (K := K) (H := H) op
          (sigmaZeroLiftBinary (K := K) (H := H) op a b) c =
        sigmaZeroLiftBinary (K := K) (H := H) op a
          (sigmaZeroLiftBinary (K := K) (H := H) op b c) := by
  intro a b c
  apply (sigmaZeroRelaxedEquiv K X H).injective
  change
    op
        (op
          (sigmaZeroForget (K := K) (X := X) (H := H) a)
          (sigmaZeroForget (K := K) (X := X) (H := H) b))
        (sigmaZeroForget (K := K) (X := X) (H := H) c) =
      op
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
        (op
          (sigmaZeroForget (K := K) (X := X) (H := H) b)
          (sigmaZeroForget (K := K) (X := X) (H := H) c))
  exact hassoc _ _ _

/-- THEOREM 6: commutativity transfers from `X` to the zero fiber. -/
theorem sigmaZeroLiftBinary_comm_of_comm
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X)
    (hcomm : ∀ x y : X, op x y = op y x) :
    ∀ a b : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroLiftBinary (K := K) (H := H) op a b =
        sigmaZeroLiftBinary (K := K) (H := H) op b a := by
  intro a b
  apply (sigmaZeroRelaxedEquiv K X H).injective
  change
    op
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
        (sigmaZeroForget (K := K) (X := X) (H := H) b) =
      op
        (sigmaZeroForget (K := K) (X := X) (H := H) b)
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
  exact hcomm _ _

/-- THEOREM 7: a left identity on `X` is a left identity on the zero fiber. -/
theorem sigmaZeroLiftBinary_left_id_of_left_id
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X) (e : X)
    (hid : ∀ x : X, op e x = x) :
    ∀ a : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroLiftBinary (K := K) (H := H) op
          (sigmaZeroEmbed (K := K) (X := X) (H := H) e) a = a := by
  intro a
  apply (sigmaZeroRelaxedEquiv K X H).injective
  change op e (sigmaZeroForget (K := K) (X := X) (H := H) a) =
    sigmaZeroForget (K := K) (X := X) (H := H) a
  exact hid _

/-- THEOREM 8: a right identity on `X` is a right identity on the zero fiber. -/
theorem sigmaZeroLiftBinary_right_id_of_right_id
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (op : X -> X -> X) (e : X)
    (hid : ∀ x : X, op x e = x) :
    ∀ a : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroLiftBinary (K := K) (H := H) op a
          (sigmaZeroEmbed (K := K) (X := X) (H := H) e) = a := by
  intro a
  apply (sigmaZeroRelaxedEquiv K X H).injective
  change op (sigmaZeroForget (K := K) (X := X) (H := H) a) e =
    sigmaZeroForget (K := K) (X := X) (H := H) a
  exact hid _

/-- Lift a predicate on `X` to the zero fiber. -/
def sigmaZeroLiftPredicate
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (P : X -> Prop) :
    SigmaRelaxedObject K X H (0 : K) -> Prop :=
  fun z => P (sigmaZeroForget (K := K) (X := X) (H := H) z)

/-- THEOREM 9: lifted predicates are exactly the original predicates on
embedded standard points. -/
theorem sigmaZeroLiftPredicate_embed
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (P : X -> Prop) (x : X) :
    sigmaZeroLiftPredicate (K := K) (H := H) P
        (sigmaZeroEmbed (K := K) (X := X) (H := H) x) ↔ P x :=
  Iff.rfl

/-- Lift a binary relation on `X` to the zero fiber. -/
def sigmaZeroLiftRelation
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (R : X -> X -> Prop) :
    SigmaRelaxedObject K X H (0 : K) ->
      SigmaRelaxedObject K X H (0 : K) -> Prop :=
  fun a b =>
    R
      (sigmaZeroForget (K := K) (X := X) (H := H) a)
      (sigmaZeroForget (K := K) (X := X) (H := H) b)

/-- THEOREM 10: lifted relations are exactly the original relations on
embedded standard points. -/
theorem sigmaZeroLiftRelation_embed
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (R : X -> X -> Prop) (x y : X) :
    sigmaZeroLiftRelation (K := K) (H := H) R
        (sigmaZeroEmbed (K := K) (X := X) (H := H) x)
        (sigmaZeroEmbed (K := K) (X := X) (H := H) y) ↔ R x y :=
  Iff.rfl

/-! ## Topological push-forward -/

/-- The zero fiber carries the topology induced by the forgetful map. -/
@[reducible]
def sigmaZeroRelaxedTopology
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    TopologicalSpace (SigmaRelaxedObject K X H (0 : K)) :=
  TopologicalSpace.induced
    (sigmaZeroForget (K := K) (X := X) (H := H)) inferInstance

/-- THEOREM 11: with the induced topology, the forgetful map is continuous. -/
theorem continuous_sigmaZeroForget_induced
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    @Continuous
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedTopology K X H) inferInstance
      (sigmaZeroForget (K := K) (X := X) (H := H)) :=
  continuous_induced_dom

/-- THEOREM 12: with the induced topology, the zero-fiber embedding is
continuous because `forget ∘ embed = id`. -/
theorem continuous_sigmaZeroEmbed_induced
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    @Continuous
      X (SigmaRelaxedObject K X H (0 : K))
      inferInstance (sigmaZeroRelaxedTopology K X H)
      (sigmaZeroEmbed (K := K) (X := X) (H := H)) := by
  rw [continuous_induced_rng]
  change Continuous (fun x : X => x)
  exact continuous_id

/-! ## Packaged certificate -/

/-- Compact certificate for the generic zero-fiber theorem. -/
structure SigmaZeroRelaxedObjectCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w) [Inhabited H] where
  zero_equiv :
    SigmaRelaxedObject K X H (0 : K) ≃ X
  headroom_irrelevant :
    ∀ (x : X) (h₁ h₂ : H),
      sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₁ =
        sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₂
  unary_push_forward :
    ∀ (f : X -> X) (z : SigmaRelaxedObject K X H (0 : K)),
      sigmaZeroForget (K := K) (X := X) (H := H)
          (sigmaZeroLiftUnary (K := K) (H := H) f z) =
        f (sigmaZeroForget (K := K) (X := X) (H := H) z)
  binary_push_forward :
    ∀ (op : X -> X -> X)
      (a b : SigmaRelaxedObject K X H (0 : K)),
      sigmaZeroForget (K := K) (X := X) (H := H)
          (sigmaZeroLiftBinary (K := K) (H := H) op a b) =
        op
          (sigmaZeroForget (K := K) (X := X) (H := H) a)
          (sigmaZeroForget (K := K) (X := X) (H := H) b)
  binary_assoc_transfer :
    ∀ (op : X -> X -> X),
      (∀ x y z : X, op (op x y) z = op x (op y z)) ->
        ∀ a b c : SigmaRelaxedObject K X H (0 : K),
          sigmaZeroLiftBinary (K := K) (H := H) op
              (sigmaZeroLiftBinary (K := K) (H := H) op a b) c =
            sigmaZeroLiftBinary (K := K) (H := H) op a
              (sigmaZeroLiftBinary (K := K) (H := H) op b c)
  binary_comm_transfer :
    ∀ (op : X -> X -> X),
      (∀ x y : X, op x y = op y x) ->
        ∀ a b : SigmaRelaxedObject K X H (0 : K),
          sigmaZeroLiftBinary (K := K) (H := H) op a b =
            sigmaZeroLiftBinary (K := K) (H := H) op b a

/-- THEOREM 12: the generic zero-fiber certificate. -/
def sigmaZeroRelaxedObjectCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w) [Inhabited H] :
    SigmaZeroRelaxedObjectCertificate K X H where
  zero_equiv := sigmaZeroRelaxedEquiv K X H
  headroom_irrelevant := sigmaZero_headroom_irrelevant (K := K)
  unary_push_forward := sigmaZeroForget_liftUnary (K := K) (H := H)
  binary_push_forward := sigmaZeroForget_liftBinary (K := K) (H := H)
  binary_assoc_transfer := sigmaZeroLiftBinary_assoc_of_assoc (K := K) (H := H)
  binary_comm_transfer := sigmaZeroLiftBinary_comm_of_comm (K := K) (H := H)

/-- Compact certificate for the topological zero-fiber theorem. -/
structure SigmaZeroRelaxedTopologyCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] where
  relaxedTopology :
    TopologicalSpace (SigmaRelaxedObject K X H (0 : K))
  forget_continuous :
    @Continuous
      (SigmaRelaxedObject K X H (0 : K)) X
      relaxedTopology inferInstance
      (sigmaZeroForget (K := K) (X := X) (H := H))
  embed_continuous :
    @Continuous
      X (SigmaRelaxedObject K X H (0 : K))
      inferInstance relaxedTopology
      (sigmaZeroEmbed (K := K) (X := X) (H := H))
  equivalence :
    SigmaRelaxedObject K X H (0 : K) ≃ X

/-- THEOREM 13: the topological zero-fiber certificate. -/
def sigmaZeroRelaxedTopologyCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    SigmaZeroRelaxedTopologyCertificate K X H where
  relaxedTopology := sigmaZeroRelaxedTopology K X H
  forget_continuous := continuous_sigmaZeroForget_induced K X H
  embed_continuous := continuous_sigmaZeroEmbed_induced K X H
  equivalence := sigmaZeroRelaxedEquiv K X H

end AffineRelaxation
end SaturationMonoid
