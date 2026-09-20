import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Basis.Prod
import H0mework.Realization.FiniteCell.FrontierCompression
import H0mework.Realization.Determinant.GradedIntegralLine

/-!
# Determinant carrier of a classified adequate canonical frontier

This is a strict downstream readout.  It accepts a positive canonical
finite-frontier classification token and reads the already generated
bounded finite-free mapping-cone candidate.  It does not accept
`Module.Free`, `Module.Finite`, a bounded model, degree support, basis,
matrix, determinant coordinate, or regulator from the caller.

The finite support is sorted canonically.  Each actual integer degree selects
the top exterior line or its dual by degree parity, so gaps and negative
degrees do not corrupt the alternating determinant.  Internal bases prove
rank one only; the public state is the graded integral line and its intrinsic
unit torsor.

Quasi-isomorphism invariance and exact-triangle coherence are later faces of
this carrier.  This readout does not promote the excluded-middle frontier
classifier into a source-generated compactness theorem.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalFrontierDeterminant

open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open GradedIntegralDeterminantLine
open scoped TensorProduct

noncomputable section

universe w

attribute [local instance] HasDerivedCategory.standard

/-- Internal rank-one line with its generated proof frame. -/
private structure RankOneIntegralLineAt : Type 1 where
  Carrier : ModuleCat.{0} ℤ
  frame : Module.Basis Unit ℤ Carrier

private noncomputable def integerLine : RankOneIntegralLineAt where
  Carrier := ModuleCat.of ℤ ℤ
  frame := Module.Basis.singleton Unit ℤ

private noncomputable def topLine
    (module : ModuleCat.{0} ℤ)
    (free : Module.Free ℤ module)
    (finite : Module.Finite ℤ module) : RankOneIntegralLineAt := by
  letI : Module.Free ℤ (module : Type) := free
  letI : Module.Finite ℤ (module : Type) := finite
  let basis := Module.finBasis ℤ (module : Type)
  exact
    { Carrier := ModuleCat.of ℤ
        (⋀[ℤ]^(Module.finrank ℤ (module : Type)) (module : Type))
      frame := determinantFrameOfBasis basis }

private noncomputable def dualLine
    (line : RankOneIntegralLineAt) : RankOneIntegralLineAt :=
  { Carrier := ModuleCat.of ℤ (Module.Dual ℤ line.Carrier)
    frame := line.frame.dualBasis }

private noncomputable def lineEquivInt
    (line : RankOneIntegralLineAt) : line.Carrier ≃ₗ[ℤ] ℤ :=
  line.frame.repr.trans (Finsupp.uniqueLinearEquiv ℤ ℤ ())

private noncomputable def tensorLine
    (left right : RankOneIntegralLineAt) : RankOneIntegralLineAt := by
  letI : Module ℤ (left.Carrier ⊗[ℤ] right.Carrier) :=
    TensorProduct.instModule
  let tensorEquiv :
      (left.Carrier ⊗[ℤ] right.Carrier) ≃ₗ[ℤ] ℤ :=
    (TensorProduct.congr (lineEquivInt left)
      (lineEquivInt right)).trans (TensorProduct.lid ℤ ℤ)
  exact
    { Carrier := ModuleCat.of ℤ (left.Carrier ⊗[ℤ] right.Carrier)
      frame := (Module.Basis.singleton Unit ℤ).map tensorEquiv.symm }

/-- Root-owned determinant readout of one classified positive branch. -/
structure RootGeneratedCanonicalFrontierDeterminantAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
    (compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence)
    (settlement : ClassifiedAdequateFrontierAt compression) : Type w where
  private mk ::

namespace RootGeneratedCanonicalFrontierDeterminantAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {settlement : ClassifiedAdequateFrontierAt compression}

def generate : RootGeneratedCanonicalFrontierDeterminantAt
    compression settlement :=
  ⟨⟩

def root
    (_face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :=
  compression.root

def candidate
    (_face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :=
  finitePerfectCandidate settlement.frontier settlement.coverage

/-- Canonically ordered finite cohomological support. -/
noncomputable def degrees
    (_face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) : List ℤ :=
  (candidateDegreeSupport settlement.frontier).sort (· ≤ ·)

private noncomputable def degreeLine
    (degree : ℤ) : RankOneIntegralLineAt := by
  let term :=
    (finitePerfectCandidate settlement.frontier settlement.coverage).X degree
  let free := candidateTermFree settlement.frontier settlement.coverage degree
  let finite := candidateTermFinite settlement.frontier settlement.coverage degree
  let top := topLine term free finite
  if degree % 2 = 0 then
    exact top
  else
    exact dualLine top

private noncomputable def determinantPackage :
    List ℤ → RankOneIntegralLineAt
  | [] => integerLine
  | degree :: tail => tensorLine (degreeLine (settlement := settlement) degree)
      (determinantPackage tail)

abbrev integralLine
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) : Type :=
  (determinantPackage (settlement := settlement) face.degrees).Carrier

private noncomputable def internalFrame
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :
    IntegralDeterminantFrame face.integralLine :=
  (determinantPackage (settlement := settlement) face.degrees).frame

noncomputable instance integralLine_free
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) : Module.Free ℤ face.integralLine :=
  Module.Free.of_basis face.internalFrame

noncomputable instance integralLine_finite
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) : Module.Finite ℤ face.integralLine :=
  Module.Finite.of_basis face.internalFrame

theorem integralLine_finrank
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :
    Module.finrank ℤ face.integralLine = 1 :=
  calc
    Module.finrank ℤ face.integralLine = Fintype.card Unit :=
      Module.finrank_eq_card_basis face.internalFrame
    _ = 1 := by simp

/-- Intrinsic integral unit torsor; no frame is installed by the caller. -/
noncomputable def unitTorsor
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :
    CanonicalIntegralUnitTorsor face.integralLine :=
  canonicalIntegralUnitTorsor face.integralLine_finrank

/-- Total rank parity of the bounded perfect candidate. -/
noncomputable def parity
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) : Fin 2 := by
  let rankAt := fun degree =>
    let _ : Module.Free ℤ (face.candidate.X degree) :=
      candidateTermFree settlement.frontier settlement.coverage degree
    let _ : Module.Finite ℤ (face.candidate.X degree) :=
      candidateTermFinite settlement.frontier settlement.coverage degree
    Module.finrank ℤ (face.candidate.X degree)
  exact ⟨(face.degrees.map rankAt).sum % 2,
    Nat.mod_lt _ (by norm_num)⟩

theorem preserves_root_candidate_and_adequacy
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement) :
    face.root = rootOccurrence ∧
      face.candidate =
        finitePerfectCandidate settlement.frontier settlement.coverage ∧
      compression.DerivedResidualVanishes
        settlement.frontier settlement.coverage :=
  ⟨rfl, rfl, settlement.residualVanishes⟩

/-- The determinant of an empty degree support is canonically the integer
line. -/
noncomputable def integralLineEquivIntOfDegreesNil
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement)
    (degreesNil : face.degrees = []) :
    face.integralLine ≃ₗ[ℤ] ℤ := by
  change (determinantPackage
    (settlement := settlement) face.degrees).Carrier ≃ₗ[ℤ] ℤ
  rw [degreesNil]
  exact LinearEquiv.refl ℤ ℤ

/-- Parity-correct determinant line of one generated candidate degree.  The
finite/free receipts and the even/odd dualization remain internal. -/
abbrev candidateDegreeDeterminantLine (degree : ℤ) :=
  (degreeLine (settlement := settlement) degree).Carrier

/-- Undualized top exterior line of one generated candidate term, with the
actual finite/free receipts passed explicitly to the internal constructor. -/
abbrev candidateIntegralTopExteriorLine (degree : ℤ) :=
  let candidate := finitePerfectCandidate
    settlement.frontier settlement.coverage
  (topLine (candidate.X degree)
    (candidateTermFree settlement.frontier settlement.coverage degree)
    (candidateTermFinite settlement.frontier settlement.coverage degree)).Carrier

noncomputable def candidateDegreeZeroEquivTop :
    candidateDegreeDeterminantLine (settlement := settlement) 0 ≃ₗ[ℤ]
      candidateIntegralTopExteriorLine (settlement := settlement) 0 :=
  LinearEquiv.refl ℤ _

noncomputable def candidateDegreeOneEquivDualTop :
    candidateDegreeDeterminantLine (settlement := settlement) 1 ≃ₗ[ℤ]
      Module.Dual ℤ
        (candidateIntegralTopExteriorLine (settlement := settlement) 1) :=
  LinearEquiv.refl ℤ _

/-- When the actual generated support is exactly cohomological degrees
`[0,1]`, expose the determinant line as the kernel/free presentation line
`det(C⁰) ⊗ det(C¹)ᵛ` (with the canonical terminal integer tensor factor).
This is a downstream decomposition of the existing line, not a new
determinant or an installed frame. -/
noncomputable def integralLineEquivDegreeZeroOne
    (face : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement)
    (degreesZeroOne : face.degrees = [0, 1]) :
    face.integralLine ≃ₗ[ℤ]
      (candidateDegreeDeterminantLine (settlement := settlement) 0 ⊗[ℤ]
        (candidateDegreeDeterminantLine (settlement := settlement) 1 ⊗[ℤ]
          ℤ)) := by
  change (determinantPackage
      (settlement := settlement) face.degrees).Carrier ≃ₗ[ℤ] _
  rw [degreesZeroOne]
  exact LinearEquiv.refl ℤ _

end RootGeneratedCanonicalFrontierDeterminantAt

/-! ## Zero-residual rigidity -/

/-- An actual zero complex generates its adequate empty frontier and hence a
canonical integral determinant state.  No classifier branch, frame or scalar
coordinate is supplied. -/
structure RootGeneratedCanonicalZeroResidualDeterminantStateAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
    (compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence)
    (actualIsZero : CategoryTheory.Limits.IsZero
      compression.actualComplex) : Type w where
  private mk ::

namespace RootGeneratedCanonicalZeroResidualDeterminantStateAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {actualIsZero : CategoryTheory.Limits.IsZero
  compression.actualComplex}

def generate : RootGeneratedCanonicalZeroResidualDeterminantStateAt
    compression actualIsZero :=
  ⟨⟩

def settlement
    (_state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) : ClassifiedAdequateFrontierAt compression :=
  compression.adequateEmptyFrontierOfActualIsZero actualIsZero

def determinantFace
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    RootGeneratedCanonicalFrontierDeterminantAt compression
      state.settlement :=
  RootGeneratedCanonicalFrontierDeterminantAt.generate

@[simp] theorem settlement_frontier
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    state.settlement.frontier = compression.emptyFrontier :=
  rfl

@[simp] theorem degrees_eq_nil
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    state.determinantFace.degrees = [] := by
  simp [RootGeneratedCanonicalFrontierDeterminantAt.degrees,
    candidateDegreeSupport, frontierDegreeSupport,
    RootGeneratedCanonicalFiniteFrontierCompressionAt.adequateEmptyFrontierOfActualIsZero,
    RootGeneratedCanonicalFiniteFrontierCompressionAt.emptyFrontier,
    settlement]

abbrev integralLine
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :=
  state.determinantFace.integralLine

/-- Canonical integral state of the zero residual determinant line. -/
noncomputable def canonicalIntegralState
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) : state.integralLine := by
  exact (state.determinantFace.integralLineEquivIntOfDegreesNil
    state.degrees_eq_nil).symm 1

theorem canonicalIntegralState_ne_zero
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    state.canonicalIntegralState ≠ 0 := by
  intro stateZero
  have coordinateZero := congrArg
    (state.determinantFace.integralLineEquivIntOfDegreesNil
      state.degrees_eq_nil) stateZero
  simp [canonicalIntegralState] at coordinateZero

theorem parity_eq_zero
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    state.determinantFace.parity = 0 := by
  apply Fin.ext
  simp [RootGeneratedCanonicalFrontierDeterminantAt.parity,
    state.degrees_eq_nil]

theorem preserves_root_and_zero_residual
    (state : RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression actualIsZero) :
    state.determinantFace.root = rootOccurrence ∧
      compression.DerivedResidualVanishes
        state.settlement.frontier state.settlement.coverage :=
  ⟨rfl, state.settlement.residualVanishes⟩

end RootGeneratedCanonicalZeroResidualDeterminantStateAt

/-! ## Derived-zero residual rigidity -/

/-- An actual acyclic complex whose zero law lives in the derived category
generates the adequate empty frontier and its determinant state.  This keeps
the actual mapping-cocone carrier while avoiding a false strict-zero premise. -/
structure RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
    (compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence)
    (actualDerivedIsZero : CategoryTheory.Limits.IsZero
      (DerivedCategory.Q.obj compression.actualComplex)) : Type w where
  private mk ::

namespace RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {actualDerivedIsZero : CategoryTheory.Limits.IsZero
  (DerivedCategory.Q.obj compression.actualComplex)}

def generate : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
    compression actualDerivedIsZero :=
  ⟨⟩

def settlement
    (_state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) : ClassifiedAdequateFrontierAt compression :=
  compression.adequateEmptyFrontierOfActualDerivedIsZero actualDerivedIsZero

def determinantFace
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    RootGeneratedCanonicalFrontierDeterminantAt compression state.settlement :=
  RootGeneratedCanonicalFrontierDeterminantAt.generate

@[simp] theorem settlement_frontier
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    state.settlement.frontier = compression.emptyFrontier :=
  rfl

@[simp] theorem degrees_eq_nil
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    state.determinantFace.degrees = [] := by
  simp [RootGeneratedCanonicalFrontierDeterminantAt.degrees,
    candidateDegreeSupport, frontierDegreeSupport,
    RootGeneratedCanonicalFiniteFrontierCompressionAt.adequateEmptyFrontierOfActualDerivedIsZero,
    RootGeneratedCanonicalFiniteFrontierCompressionAt.emptyFrontier,
    settlement]

abbrev integralLine
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :=
  state.determinantFace.integralLine

/-- Canonical state of the generated empty perfect replacement. -/
noncomputable def canonicalIntegralState
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) : state.integralLine :=
  (state.determinantFace.integralLineEquivIntOfDegreesNil
    state.degrees_eq_nil).symm 1

theorem canonicalIntegralState_ne_zero
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    state.canonicalIntegralState ≠ 0 := by
  intro stateZero
  have coordinateZero := congrArg
    (state.determinantFace.integralLineEquivIntOfDegreesNil
      state.degrees_eq_nil) stateZero
  simp [canonicalIntegralState] at coordinateZero

theorem parity_eq_zero
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    state.determinantFace.parity = 0 := by
  apply Fin.ext
  simp [RootGeneratedCanonicalFrontierDeterminantAt.parity,
    state.degrees_eq_nil]

theorem preserves_root_and_derived_zero_residual
    (state : RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt
      compression actualDerivedIsZero) :
    state.determinantFace.root = rootOccurrence ∧
      CategoryTheory.Limits.IsZero
        (DerivedCategory.Q.obj compression.actualComplex) ∧
      compression.DerivedResidualVanishes
        state.settlement.frontier state.settlement.coverage :=
  ⟨rfl, actualDerivedIsZero, state.settlement.residualVanishes⟩

end RootGeneratedCanonicalDerivedZeroResidualDeterminantStateAt

end

end CanonicalFrontierDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
