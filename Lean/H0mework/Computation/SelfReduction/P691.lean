import H0mework.Computation.SelfReduction.P690

/-!
# Proposition 691: SAT as multi-path bumpSat plus satOr merge

P690 proves one certified descent path: local good-cover primitives plus
overlap-consistent descent give one discrete CNF witness.

The solver shape is not a single SVD vector, not a single bit flip, and not a
single chart correction.  The framework shape is:

* many local/phase paths run their own bumpSat convergence;
* their path rates are merged by the same noisy-OR/satOr monoid as salience;
* a descent certificate turns the merged support into one Boolean assignment.

This file formalizes that shape.  It still does not prove `P = NP`, nor that a
runtime can always generate enough paths, nor that the merge/descent certificate
is polynomial.  It proves the exact bridge: once multi-path satOr support is
faithful to satisfiability and descends soundly, the merged producer emits a
verified SAT witness exactly when the CNF is satisfiable.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

/-! ## Finite satOr merge -/

/-- Fold a finite family of saturation rates by noisy-OR.  The empty merge is
the no-op rate `0`. -/
def satOrList : List ℤ -> ℤ
  | [] => 0
  | σ :: rest => satOr σ (satOrList rest)

@[simp] theorem satOrList_nil : satOrList [] = 0 := rfl

@[simp] theorem satOrList_cons (σ : ℤ) (rest : List ℤ) :
    satOrList (σ :: rest) = satOr σ (satOrList rest) := rfl

/-- THEOREM 1: finite satOr merge composes by the same monoid law. -/
theorem satOrList_append (xs ys : List ℤ) :
    satOrList (xs ++ ys) = satOr (satOrList xs) (satOrList ys) := by
  induction xs with
  | nil =>
      simp [satOrList, satOr_zero_left]
  | cons σ rest ih =>
      simp [satOrList, ih]
      rw [← satOr_assoc]

/-! ## BumpSat paths -/

/-- One SAT phase path: it has a bumpSat-generated rate and a Boolean sign
assignment.  When the path is active, its assignment verifies the formula.

The theorem deliberately uses `bumpSat` to tie path support back to the
saturation algebra; later runtime work owns how SVD/phase data chooses
`initialHeadroom`, `sigma`, and the assignment.
-/
structure CNFBumpSatPath {n : Nat} (formula : CNFFormula n) where
  initialHeadroom : ℤ
  sigma : ℤ
  assignment : Nat -> Bool
  verified_if_active :
    bumpSat initialHeadroom sigma ≠ 0 ->
      CNFSATVerify formula (CNFSATNode.root n) assignment

namespace CNFBumpSatPath

variable {n : Nat} {formula : CNFFormula n}

/-- The path support rate produced by one bumpSat convergence channel. -/
def rate (p : CNFBumpSatPath formula) : ℤ :=
  bumpSat p.initialHeadroom p.sigma

/-- THEOREM 2: active path support gives a verified CNF root assignment. -/
theorem verified_of_active (p : CNFBumpSatPath formula)
    (h : p.rate ≠ 0) :
    CNFSATVerify formula (CNFSATNode.root n) p.assignment :=
  p.verified_if_active h

end CNFBumpSatPath

/-! ## P690 single paths as bumpSat paths -/

universe u

variable {Index E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited Index]

namespace CNFGoodCoverPrimitiveDescent

variable {n : Nat} {formula : CNFFormula n}
variable (D : CNFGoodCoverPrimitiveDescent formula Index E F)

/-- THEOREM 3: a P690 good-cover descent is one fully active bumpSat path.

It uses the absorbing rate `1` only as a packaging bridge: P690 already proved
the assignment, while P691 records that single certified paths can enter the
multi-path satOr merge surface.
-/
def toBumpSatPath : CNFBumpSatPath formula where
  initialHeadroom := 0
  sigma := 1
  assignment := D.descentAssignment
  verified_if_active := by
    intro _hactive
    exact D.root_verified

/-- THEOREM 4: the packaging path has saturated rate one. -/
theorem toBumpSatPath_rate :
    D.toBumpSatPath.rate = 1 := by
  simp [toBumpSatPath, CNFBumpSatPath.rate, bumpSat]

end CNFGoodCoverPrimitiveDescent

/-! ## Multi-path satOr merge producer -/

/-- Multi-path SAT solver certificate.

The paths run in parallel; their bumpSat rates are merged by `satOrList`.  The
hard producer obligations are explicit:

* nonzero merged support descends soundly to one Boolean assignment;
* satisfiable formulas make the merged support nonzero.
-/
structure CNFMultiPathSatOrMerge {n : Nat} (formula : CNFFormula n) where
  paths : List (CNFBumpSatPath formula)
  mergedAssignment : Nat -> Bool
  descent_sound :
    satOrList (paths.map CNFBumpSatPath.rate) ≠ 0 ->
      CNFSATVerify formula (CNFSATNode.root n) mergedAssignment
  merge_complete :
    CNFSatisfiable formula ->
      satOrList (paths.map CNFBumpSatPath.rate) ≠ 0

namespace CNFMultiPathSatOrMerge

variable {n : Nat} {formula : CNFFormula n}
variable (M : CNFMultiPathSatOrMerge formula)

/-- The merged multi-path support rate. -/
def mergedRate : ℤ :=
  satOrList (M.paths.map CNFBumpSatPath.rate)

/-- THEOREM 5: appending a second path family merges supports by satOr. -/
theorem mergedRate_append
    (left right : List (CNFBumpSatPath formula)) :
    satOrList ((left ++ right).map CNFBumpSatPath.rate) =
      satOr
        (satOrList (left.map CNFBumpSatPath.rate))
        (satOrList (right.map CNFBumpSatPath.rate)) := by
  rw [List.map_append]
  exact satOrList_append
    (left.map CNFBumpSatPath.rate) (right.map CNFBumpSatPath.rate)

/-- The merged producer emits the descended assignment exactly when the merged
satOr support is nonzero. -/
def rootProducer : Option (Nat -> Bool) :=
  if M.mergedRate ≠ 0 then
    some M.mergedAssignment
  else
    none

/-- THEOREM 6: the multi-path merged producer is sound. -/
theorem rootProducer_sound {assignment : Nat -> Bool}
    (h : M.rootProducer = some assignment) :
    CNFSATVerify formula (CNFSATNode.root n) assignment := by
  by_cases hactive : M.mergedRate ≠ 0
  · have hsome : some M.mergedAssignment = some assignment := by
      simpa [rootProducer, hactive] using h
    have heq : M.mergedAssignment = assignment := by
      simpa using Option.some.inj hsome
    rw [← heq]
    exact M.descent_sound hactive
  · have : False := by
      simp [rootProducer, hactive] at h
    exact False.elim this

/-- THEOREM 7: if the formula is satisfiable, the multi-path merge emits a
witness. -/
theorem rootProducer_complete
    (h : CNFSatisfiable formula) :
    ∃ assignment : Nat -> Bool, M.rootProducer = some assignment := by
  have hactive : M.mergedRate ≠ 0 := M.merge_complete h
  exact ⟨M.mergedAssignment, by simp [rootProducer, hactive]⟩

/-- THEOREM 8: a multi-path satOr merge is a P684 root witness-producer
projection. -/
def toRootWitnessProducerProjection :
    WitnessProducerProjection Unit (Nat -> Bool) where
  verify := fun _ assignment =>
    CNFSATVerify formula (CNFSATNode.root n) assignment
  producer := fun _ => M.rootProducer
  sound := by
    intro _ assignment h
    exact M.rootProducer_sound h
  complete := by
    intro _ h
    have hs : CNFSatisfiable formula :=
      (cnfRoot_hasWitness_iff_satisfiable formula).1 h
    exact M.rootProducer_complete hs

/-- THEOREM 9: multi-path bumpSat + satOr merge emits a verified witness iff
the CNF formula is satisfiable. -/
theorem producedVerifiedWitness_iff_satisfiable :
    M.toRootWitnessProducerProjection.ProducedVerifiedWitness () ↔
      CNFSatisfiable formula := by
  rw [M.toRootWitnessProducerProjection.producedVerifiedWitness_iff_hasWitness]
  exact cnfRoot_hasWitness_iff_satisfiable formula

end CNFMultiPathSatOrMerge

/-! ## Packaged certificate -/

/-- P691 certificate: the correct SAT solver surface is multi-path bumpSat
followed by satOr support merge and certified descent. -/
structure MultiPathSatOrSATCertificate where
  p690_good_cover_root :
    GoodCoverPrimitiveDescentSATCertificate.{0}
  sat_or_finite_append :
    ∀ xs ys : List ℤ,
      satOrList (xs ++ ys) = satOr (satOrList xs) (satOrList ys)
  to_root_projection :
    ∀ {n : Nat} {formula : CNFFormula n}
      (_ : CNFMultiPathSatOrMerge formula),
      WitnessProducerProjection Unit (Nat -> Bool)
  root_producer_iff_satisfiable :
    ∀ {n : Nat} {formula : CNFFormula n}
      (M : CNFMultiPathSatOrMerge formula),
      M.toRootWitnessProducerProjection.ProducedVerifiedWitness () ↔
        CNFSatisfiable formula

/-- DEFINITION 1: canonical P691 multi-path satOr SAT certificate. -/
def multiPathSatOrSATCertificate :
    MultiPathSatOrSATCertificate where
  p690_good_cover_root := goodCoverPrimitiveDescentSATCertificate
  sat_or_finite_append := satOrList_append
  to_root_projection := by
    intro n formula M
    exact M.toRootWitnessProducerProjection
  root_producer_iff_satisfiable := by
    intro n formula M
    exact M.producedVerifiedWitness_iff_satisfiable

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P691 grand root: multi-path bumpSat convergence plus finite satOr merge is
the solver-shaped certificate surface, with P690 as the single-path descent
subroutine.
-/
structure MultiPathSatOrSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p690_root :
    GoodCoverPrimitiveDescentSATUnifiedRootCertificate.{u, v, w, z} E0
  multi_path_sat_or :
    MultiPathSatOrSATCertificate

/-- THEOREM 10: the multi-path satOr SAT unified root is inhabited. -/
def multiPathSatOrSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    MultiPathSatOrSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p690_root := goodCoverPrimitiveDescentSATUnifiedRootCertificate (E0 := E0)
  multi_path_sat_or := multiPathSatOrSATCertificate

end GrandUnification

end SaturationMonoid
