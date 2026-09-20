import Mathlib.GroupTheory.QuotientGroup.Basic
import H0mework.Realization.GlobalSections.KernelIncidenceRigidity

/-!
# Generic prime-power quotient evaluation kernel

For an additive group `G`, this kernel evaluates an element simultaneously in
every actual prime-power quotient `G / p^k G`.  The quotient laws generate
zero, addition, and naturality.  A zero quotient class generates membership
in the corresponding multiplication range, from which an actual division
root is extracted and packaged for the frozen prime-power rigidity engine.

The kernel owns no domain carrier and accepts no global finite-generation
premise.  A rooted domain presentation must generate `AddGroup.FG G` before
forming the final incidence material.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace PrimePowerQuotientEvaluation

open PrimePowerKernelIncidenceRigidity

noncomputable section

universe u v

variable (G : Type u) [AddCommGroup G]

abbrev multiplicationRange (prime : Nat.Primes) (exponent : Nat) :
    AddSubgroup G :=
  (nsmulAddMonoidHom ((prime : Nat) ^ exponent : Nat)).range

/-- One actual prime-power quotient. -/
abbrev Quotient (prime : Nat.Primes) (exponent : Nat) : Type u :=
  G ⧸ multiplicationRange G prime exponent

/-- Whole family of actual finite prime-power restrictions. -/
abbrev State : Type u :=
  (prime : Nat.Primes) → (exponent : Nat) → Quotient G prime exponent

/-- Canonical quotient-family evaluator. -/
def evaluator (element : G) : State G :=
  fun prime exponent =>
    QuotientAddGroup.mk' (multiplicationRange G prime exponent) element

@[simp] theorem evaluator_zero : evaluator G 0 = 0 := by
  funext prime exponent
  rfl

@[simp] theorem evaluator_add (left right : G) :
    evaluator G (left + right) = evaluator G left + evaluator G right := by
  funext prime exponent
  exact map_add (QuotientAddGroup.mk' (multiplicationRange G prime exponent))
    left right

@[simp] theorem evaluator_neg (element : G) :
    evaluator G (-element) = -evaluator G element := by
  funext prime exponent
  exact map_neg (QuotientAddGroup.mk' (multiplicationRange G prime exponent))
    element

@[simp] theorem evaluator_sub (left right : G) :
    evaluator G (left - right) = evaluator G left - evaluator G right := by
  rw [sub_eq_add_neg, evaluator_add, evaluator_neg, sub_eq_add_neg]

/-- Equality of two whole quotient readouts is quotient-zero for their
difference; the following range and division-root steps remain internal to
this kernel. -/
theorem evaluatorDifferenceZeroOfEq
    {left right : G} (equalReadout : evaluator G left = evaluator G right) :
    evaluator G (left - right) = 0 := by
  rw [evaluator_sub, equalReadout, sub_self]

variable {G}
variable {H : Type v} [AddCommGroup H]

/-- Any additive map descends through matching prime-power quotients. -/
def quotientMap (map : G →+ H) (prime : Nat.Primes) (exponent : Nat) :
    Quotient G prime exponent →+ Quotient H prime exponent :=
  QuotientAddGroup.map
    (multiplicationRange G prime exponent)
    (multiplicationRange H prime exponent)
    map (by
      rintro _ ⟨element, rfl⟩
      refine ⟨map element, ?_⟩
      exact (map.map_nsmul ((prime : Nat) ^ exponent) element).symm)

/-- Prime-power quotient evaluation is natural in the additive carrier. -/
@[simp] theorem evaluator_naturality
    (map : G →+ H) (element : G)
    (prime : Nat.Primes) (exponent : Nat) :
    quotientMap map prime exponent (evaluator G element prime exponent) =
      evaluator H (map element) prime exponent :=
  rfl

variable (G)

/-- A zero quotient class is exactly membership in the multiplication range. -/
theorem rangeMembershipOfQuotientZero
    (element : G) (prime : Nat.Primes) (exponent : Nat)
    (quotientZero : evaluator G element prime exponent = 0) :
    element ∈ multiplicationRange G prime exponent :=
  (QuotientAddGroup.eq_zero_iff element).mp quotientZero

/-- Multiplication-range membership contains an actual landing root. -/
def divisionRootOfRangeMembership
    (element : G) (prime : Nat.Primes) (exponent : Nat)
    (membership : element ∈ multiplicationRange G prime exponent) :
    { root : G // (prime : Nat) ^ exponent • root = element } := by
  rw [AddMonoidHom.mem_range] at membership
  exact ⟨Classical.choose membership, Classical.choose_spec membership⟩

/-- Whole-evaluator zero generates the actual `p^k` root required by the
frozen rigidity engine. -/
def divisionRoot
    (element : G) (evaluatorZero : evaluator G element = 0)
    (prime : Nat.Primes) (exponent : Nat) (_exponentPositive : 0 < exponent) :
    { root : G // (prime : Nat) ^ exponent • root = element } :=
  divisionRootOfRangeMembership G element prime exponent
    (rangeMembershipOfQuotientZero G element prime exponent
      (congrFun (congrFun evaluatorZero prime) exponent))

/-- Final incidence material after a rooted finite presentation has generated
finite generation. -/
def incidenceMaterial (finiteGenerated : AddGroup.FG G) :
    PrimePowerKernelIncidenceAt G (State G) where
  evaluator := evaluator G
  zeroLanding := evaluator_zero G
  additionLanding := evaluator_add G
  finiteGenerated := finiteGenerated
  divisionRoot := divisionRoot G

theorem incidenceMaterial_evaluator
    (finiteGenerated : AddGroup.FG G) :
    (incidenceMaterial G finiteGenerated).evaluator = evaluator G :=
  rfl

/-! ## Exact-occurrence installation -/

universe w

/-- Root authority for the generic quotient evaluator.  The evaluator and
its incidence material are generated by folding the canonical quotient law
over this exact occurrence; the domain supplies only its actual carrier and
the finite-generation fact generated by its presentation. -/
structure RootGeneratedPrimePowerQuotientEvaluationAt
    {Root : Type w}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (finiteGenerated : AddGroup.FG G) : Type (max u w) where
  private mk ::

namespace RootGeneratedPrimePowerQuotientEvaluationAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {finiteGenerated : AddGroup.FG G}

def generate :
    RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated :=
  ⟨⟩

/-- Local universal law installed at every accounted occurrence. -/
def evaluatorAlgebra
    (_root : Root) (_children : List (G → State G)) : G → State G :=
  PrimePowerQuotientEvaluation.evaluator G

/-- The canonical quotient evaluator as the unique fold of the installed
local law over the exact occurrence. -/
def accountedEvaluator
    (_face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) : G → State G :=
  rootOccurrence.fold (evaluatorAlgebra G)

@[simp] theorem accountedEvaluator_eq_canonical
    (face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) :
    face.accountedEvaluator = PrimePowerQuotientEvaluation.evaluator G := by
  cases rootOccurrence
  rfl

/-- Generic packaging of the fold-generated evaluator into the frozen
prime-power incidence mouth. -/
def material
    (face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) :
    PrimePowerKernelIncidenceAt G (State G) where
  evaluator := face.accountedEvaluator
  zeroLanding := by
    rw [face.accountedEvaluator_eq_canonical]
    exact evaluator_zero G
  additionLanding := by
    intro left right
    rw [face.accountedEvaluator_eq_canonical]
    exact evaluator_add G left right
  finiteGenerated := finiteGenerated
  divisionRoot := by
    intro element evaluatorZero prime exponent exponentPositive
    apply PrimePowerQuotientEvaluation.divisionRoot G element
      _ prime exponent exponentPositive
    simpa only [face.accountedEvaluator_eq_canonical] using evaluatorZero

/-- Install the generic material together with the exact root point in one
dependent occurrence. -/
def dependentOccurrence
    (face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) :
    RootedAccountedUnfolding
      (Root × PrimePowerKernelIncidenceAt G (State G)) :=
  rootOccurrence.map fun root ↦ (root, face.material)

theorem dependentOccurrence_projects_to_root
    (face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) :
    face.dependentOccurrence.map Prod.fst = rootOccurrence := by
  rw [dependentOccurrence, RootedAccountedUnfolding.map_map]
  change rootOccurrence.map id = rootOccurrence
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem material_evaluator
    (face : RootGeneratedPrimePowerQuotientEvaluationAt G
      rootOccurrence finiteGenerated) :
    face.material.evaluator = face.accountedEvaluator :=
  rfl

end RootGeneratedPrimePowerQuotientEvaluationAt

end


end PrimePowerQuotientEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
