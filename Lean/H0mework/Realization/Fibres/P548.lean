import H0mework.Realization.Fibres.P547

/-!
# Proposition 548: the eighteen-object sigma-zero fiber table

P537 introduced the finite index of eighteen core mathematical objects.
P547 proved the generic object-level theorem:

`SigmaRelaxedObject K X H 0 ≃ X`.

This file connects the two.  It assigns each core-object index a concrete
standard carrier type and proves that every listed object has the same
sigma-zero annealing face:

* the zero-fiber forgetful map is bijective;
* headroom is irrelevant at `sigma = 0`;
* unary and binary operations push forward to the standard carrier operation;
* associativity and commutativity transfer from the carrier to the zero fiber.

Boundary: this is the zero-fiber table.  It does not claim that every listed
object's full higher structure has already been rebuilt for nonzero `sigma`.
It proves the uniform base theorem needed before those nonzero structures can
be added without drifting away from standard mathematics.
-/

noncomputable section

namespace SaturationMonoid

open AffineRelaxation

/-! ## Standard carriers for the eighteen-object table -/

/-- A concrete standard carrier for each object in the P537 eighteen-object
index.  These carriers are deliberately modest: the theorem proved here is the
zero-fiber carrier equivalence, while richer group/ring/topological/category
structure remains supplied by the corresponding standard Mathlib structures. -/
abbrev CoreObjectCarrier : CoreMathematicalObject18 -> Type
  | .naturalNumbers => ℕ
  | .integers => ℤ
  | .rationals => ℚ
  | .groups => Multiplicative ℤ
  | .rings => ℤ
  | .fields => ℚ
  | .topologicalSpaces => ℝ
  | .metricSpaces => ℝ
  | .manifolds => ℝ
  | .fiberBundles => ℝ × ℝ
  | .categories => PUnit
  | .chainComplexes => ℤ × ℤ
  | .derivedCategories => ℤ
  | .realNumbers => ℝ
  | .probabilityMeasures => ℝ
  | .hilbertSpaces => ℂ
  | .saturatedHoTT => PUnit
  | .riemannZeta => ℂ

instance coreObjectCarrierInhabited
    (O : CoreMathematicalObject18) : Inhabited (CoreObjectCarrier O) := by
  cases O <;> infer_instance

instance coreObjectCarrierTopologicalSpace
    (O : CoreMathematicalObject18) :
    TopologicalSpace (CoreObjectCarrier O) := by
  cases O <;> infer_instance

/-- The shared headroom coordinate used by the core-object zero-fiber table. -/
abbrev CoreObjectHeadroom : Type := ℝ

/-- The sigma-zero relaxed fiber for a listed mathematical object. -/
abbrev CoreObjectSigmaZeroFiber (O : CoreMathematicalObject18) : Type :=
  SigmaRelaxedObject ℝ (CoreObjectCarrier O) CoreObjectHeadroom (0 : ℝ)

/-! ## Per-object zero-fiber maps -/

/-- Forget the headroom coordinate from a core object's zero fiber. -/
def coreObjectSigmaZeroForget (O : CoreMathematicalObject18) :
    CoreObjectSigmaZeroFiber O -> CoreObjectCarrier O :=
  sigmaZeroForget
    (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)

/-- Embed a core object's standard carrier into its zero fiber. -/
def coreObjectSigmaZeroEmbed (O : CoreMathematicalObject18) :
    CoreObjectCarrier O -> CoreObjectSigmaZeroFiber O :=
  sigmaZeroEmbed
    (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)

/-- THEOREM 1: every core object's zero fiber is equivalent to its standard
carrier. -/
def coreObjectSigmaZeroEquiv (O : CoreMathematicalObject18) :
    CoreObjectSigmaZeroFiber O ≃ CoreObjectCarrier O :=
  sigmaZeroRelaxedEquiv ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZeroForget_embed
    (O : CoreMathematicalObject18) (x : CoreObjectCarrier O) :
    coreObjectSigmaZeroForget O (coreObjectSigmaZeroEmbed O x) = x :=
  rfl

@[simp] theorem coreObjectSigmaZeroEmbed_forget
    (O : CoreMathematicalObject18) (z : CoreObjectSigmaZeroFiber O) :
    coreObjectSigmaZeroEmbed O (coreObjectSigmaZeroForget O z) = z :=
  sigmaZeroEmbed_forget
    (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom) z

/-- THEOREM 2: the forgetful map is a bijection for every object in the
eighteen-object table. -/
theorem coreObjectSigmaZeroForget_bijective
    (O : CoreMathematicalObject18) :
    Function.Bijective (coreObjectSigmaZeroForget O) := by
  constructor
  · intro a b h
    exact (coreObjectSigmaZeroEquiv O).injective h
  · intro x
    exact ⟨coreObjectSigmaZeroEmbed O x, rfl⟩

/-- THEOREM 3: at `sigma = 0`, the headroom coordinate is irrelevant for every
listed object. -/
theorem coreObjectSigmaZero_headroom_irrelevant
    (O : CoreMathematicalObject18)
    (x : CoreObjectCarrier O) (h₁ h₂ : CoreObjectHeadroom) :
    sigmaRelaxedMk (K := ℝ) (σ := (0 : ℝ)) x h₁ =
      sigmaRelaxedMk (K := ℝ) (σ := (0 : ℝ)) x h₂ :=
  sigmaZero_headroom_irrelevant (K := ℝ) x h₁ h₂

/-! ## Structure transport on the table -/

/-- Lift a unary operation on a core object's carrier to its zero fiber. -/
def coreObjectSigmaZeroLiftUnary
    (O : CoreMathematicalObject18)
    (f : CoreObjectCarrier O -> CoreObjectCarrier O) :
    CoreObjectSigmaZeroFiber O -> CoreObjectSigmaZeroFiber O :=
  sigmaZeroLiftUnary (K := ℝ) (H := CoreObjectHeadroom) f

/-- THEOREM 4: unary operations push forward to their standard operation. -/
@[simp] theorem coreObjectSigmaZeroForget_liftUnary
    (O : CoreMathematicalObject18)
    (f : CoreObjectCarrier O -> CoreObjectCarrier O)
    (z : CoreObjectSigmaZeroFiber O) :
    coreObjectSigmaZeroForget O
        (coreObjectSigmaZeroLiftUnary O f z) =
      f (coreObjectSigmaZeroForget O z) :=
  rfl

/-- Lift a binary operation on a core object's carrier to its zero fiber. -/
def coreObjectSigmaZeroLiftBinary
    (O : CoreMathematicalObject18)
    (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O) :
    CoreObjectSigmaZeroFiber O -> CoreObjectSigmaZeroFiber O ->
      CoreObjectSigmaZeroFiber O :=
  sigmaZeroLiftBinary (K := ℝ) (H := CoreObjectHeadroom) op

/-- THEOREM 5: binary operations push forward to their standard operation. -/
@[simp] theorem coreObjectSigmaZeroForget_liftBinary
    (O : CoreMathematicalObject18)
    (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O)
    (a b : CoreObjectSigmaZeroFiber O) :
    coreObjectSigmaZeroForget O
        (coreObjectSigmaZeroLiftBinary O op a b) =
      op (coreObjectSigmaZeroForget O a) (coreObjectSigmaZeroForget O b) :=
  rfl

/-- THEOREM 6: associativity transfers from a carrier operation to its zero
fiber operation for every core object. -/
theorem coreObjectSigmaZeroLiftBinary_assoc_of_assoc
    (O : CoreMathematicalObject18)
    (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O)
    (hassoc :
      ∀ x y z : CoreObjectCarrier O, op (op x y) z = op x (op y z)) :
    ∀ a b c : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroLiftBinary O op
          (coreObjectSigmaZeroLiftBinary O op a b) c =
        coreObjectSigmaZeroLiftBinary O op a
          (coreObjectSigmaZeroLiftBinary O op b c) :=
  sigmaZeroLiftBinary_assoc_of_assoc
    (K := ℝ) (H := CoreObjectHeadroom) op hassoc

/-- THEOREM 7: commutativity transfers from a carrier operation to its zero
fiber operation for every core object. -/
theorem coreObjectSigmaZeroLiftBinary_comm_of_comm
    (O : CoreMathematicalObject18)
    (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O)
    (hcomm :
      ∀ x y : CoreObjectCarrier O, op x y = op y x) :
    ∀ a b : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroLiftBinary O op a b =
        coreObjectSigmaZeroLiftBinary O op b a :=
  sigmaZeroLiftBinary_comm_of_comm
    (K := ℝ) (H := CoreObjectHeadroom) op hcomm

/-- Lift a predicate on a core object's carrier to its zero fiber. -/
def coreObjectSigmaZeroLiftPredicate
    (O : CoreMathematicalObject18)
    (P : CoreObjectCarrier O -> Prop) :
    CoreObjectSigmaZeroFiber O -> Prop :=
  sigmaZeroLiftPredicate (K := ℝ) (H := CoreObjectHeadroom) P

/-- THEOREM 8: predicates pull back exactly along the zero-fiber embedding. -/
theorem coreObjectSigmaZeroLiftPredicate_embed
    (O : CoreMathematicalObject18)
    (P : CoreObjectCarrier O -> Prop) (x : CoreObjectCarrier O) :
    coreObjectSigmaZeroLiftPredicate O P
        (coreObjectSigmaZeroEmbed O x) ↔ P x :=
  Iff.rfl

/-- Lift a relation on a core object's carrier to its zero fiber. -/
def coreObjectSigmaZeroLiftRelation
    (O : CoreMathematicalObject18)
    (R : CoreObjectCarrier O -> CoreObjectCarrier O -> Prop) :
    CoreObjectSigmaZeroFiber O -> CoreObjectSigmaZeroFiber O -> Prop :=
  sigmaZeroLiftRelation (K := ℝ) (H := CoreObjectHeadroom) R

/-- THEOREM 9: relations pull back exactly along the zero-fiber embedding. -/
theorem coreObjectSigmaZeroLiftRelation_embed
    (O : CoreMathematicalObject18)
    (R : CoreObjectCarrier O -> CoreObjectCarrier O -> Prop)
    (x y : CoreObjectCarrier O) :
    coreObjectSigmaZeroLiftRelation O R
        (coreObjectSigmaZeroEmbed O x)
        (coreObjectSigmaZeroEmbed O y) ↔ R x y :=
  Iff.rfl

/-- THEOREM 10: every core object receives the generic P547 zero-fiber object
certificate. -/
def coreObjectSigmaZeroGenericCertificate
    (O : CoreMathematicalObject18) :
    SigmaZeroRelaxedObjectCertificate
      ℝ (CoreObjectCarrier O) CoreObjectHeadroom :=
  sigmaZeroRelaxedObjectCertificate
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 11: every core object receives the P547 induced-topology
certificate. -/
def coreObjectSigmaZeroTopologyCertificate
    (O : CoreMathematicalObject18) :
    SigmaZeroRelaxedTopologyCertificate
      ℝ (CoreObjectCarrier O) CoreObjectHeadroom :=
  sigmaZeroRelaxedTopologyCertificate
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-! ## Packaged table certificate -/

/-- Compact table certificate connecting the P537 eighteen-object index to the
P547 generic zero-fiber theorem. -/
structure CoreObjectSigmaZeroFiberTableCertificate where
  object_count :
    Fintype.card CoreMathematicalObject18 = 18
  zero_equiv :
    ∀ O : CoreMathematicalObject18,
      CoreObjectSigmaZeroFiber O ≃ CoreObjectCarrier O
  forget_bijective :
    ∀ O : CoreMathematicalObject18,
      Function.Bijective (coreObjectSigmaZeroForget O)
  headroom_irrelevant :
    ∀ (O : CoreMathematicalObject18)
      (x : CoreObjectCarrier O) (h₁ h₂ : CoreObjectHeadroom),
      sigmaRelaxedMk (K := ℝ) (σ := (0 : ℝ)) x h₁ =
        sigmaRelaxedMk (K := ℝ) (σ := (0 : ℝ)) x h₂
  unary_push_forward :
    ∀ (O : CoreMathematicalObject18)
      (f : CoreObjectCarrier O -> CoreObjectCarrier O)
      (z : CoreObjectSigmaZeroFiber O),
      coreObjectSigmaZeroForget O
          (coreObjectSigmaZeroLiftUnary O f z) =
        f (coreObjectSigmaZeroForget O z)
  binary_push_forward :
    ∀ (O : CoreMathematicalObject18)
      (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O)
      (a b : CoreObjectSigmaZeroFiber O),
      coreObjectSigmaZeroForget O
          (coreObjectSigmaZeroLiftBinary O op a b) =
        op (coreObjectSigmaZeroForget O a) (coreObjectSigmaZeroForget O b)
  assoc_transfer :
    ∀ (O : CoreMathematicalObject18)
      (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O),
      (∀ x y z : CoreObjectCarrier O, op (op x y) z = op x (op y z)) ->
        ∀ a b c : CoreObjectSigmaZeroFiber O,
          coreObjectSigmaZeroLiftBinary O op
              (coreObjectSigmaZeroLiftBinary O op a b) c =
            coreObjectSigmaZeroLiftBinary O op a
              (coreObjectSigmaZeroLiftBinary O op b c)
  comm_transfer :
    ∀ (O : CoreMathematicalObject18)
      (op : CoreObjectCarrier O -> CoreObjectCarrier O -> CoreObjectCarrier O),
      (∀ x y : CoreObjectCarrier O, op x y = op y x) ->
        ∀ a b : CoreObjectSigmaZeroFiber O,
          coreObjectSigmaZeroLiftBinary O op a b =
            coreObjectSigmaZeroLiftBinary O op b a
  predicate_pullback :
    ∀ (O : CoreMathematicalObject18)
      (P : CoreObjectCarrier O -> Prop) (x : CoreObjectCarrier O),
      coreObjectSigmaZeroLiftPredicate O P
          (coreObjectSigmaZeroEmbed O x) ↔ P x
  relation_pullback :
    ∀ (O : CoreMathematicalObject18)
      (R : CoreObjectCarrier O -> CoreObjectCarrier O -> Prop)
      (x y : CoreObjectCarrier O),
      coreObjectSigmaZeroLiftRelation O R
          (coreObjectSigmaZeroEmbed O x)
          (coreObjectSigmaZeroEmbed O y) ↔ R x y
  generic_p547_certificate :
    ∀ O : CoreMathematicalObject18,
      SigmaZeroRelaxedObjectCertificate
        ℝ (CoreObjectCarrier O) CoreObjectHeadroom
  topology_p547_certificate :
    ∀ O : CoreMathematicalObject18,
      SigmaZeroRelaxedTopologyCertificate
        ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 12: the complete eighteen-object zero-fiber table is inhabited. -/
def coreObjectSigmaZeroFiberTableCertificate :
    CoreObjectSigmaZeroFiberTableCertificate where
  object_count := coreMathematicalObject18_card
  zero_equiv := coreObjectSigmaZeroEquiv
  forget_bijective := coreObjectSigmaZeroForget_bijective
  headroom_irrelevant := coreObjectSigmaZero_headroom_irrelevant
  unary_push_forward := coreObjectSigmaZeroForget_liftUnary
  binary_push_forward := coreObjectSigmaZeroForget_liftBinary
  assoc_transfer := coreObjectSigmaZeroLiftBinary_assoc_of_assoc
  comm_transfer := coreObjectSigmaZeroLiftBinary_comm_of_comm
  predicate_pullback := coreObjectSigmaZeroLiftPredicate_embed
  relation_pullback := coreObjectSigmaZeroLiftRelation_embed
  generic_p547_certificate := coreObjectSigmaZeroGenericCertificate
  topology_p547_certificate := coreObjectSigmaZeroTopologyCertificate

end SaturationMonoid
