import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.GroupTheory.Coset.Card
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated finite-defect determinant calculus

An actual map between finite free integral lattice presentations generates
its kernel, range, cokernel and two-term cofiber carrier.  A downstream
calculation receipt supplies only facts generated from that presentation:
equal integral rank and finiteness of the actual cokernel.  The generic
kernel then proves injectivity, constructs the range basis internally, and
identifies every installed-frame determinant with the cokernel cardinality.

The finite homotopy-cardinality readout keeps kernel and cokernel as separate
generated defects.  In the present equal-rank free-lattice case the finite
kernel is forced to be trivial, so

`|det f| = |coker f| / |ker f|`.

No kernel, cokernel, matrix, basis, determinant value or cardinality is a
field of the source face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace FiniteDefectDeterminant

universe u v w

/-- Root-owned actual integral presentation map. -/
structure RootGeneratedFiniteDefectPresentationAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [AddCommGroup Target]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (sourceOccurrences : Source → RootedAccountedUnfolding Source)
    (targetOccurrences : Target → RootedAccountedUnfolding Target)
    (mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)) : Type where
  private mk ::

namespace RootGeneratedFiniteDefectPresentationAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [AddCommGroup Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)}

def generate : RootGeneratedFiniteDefectPresentationAt rootOccurrence
    sourceOccurrences targetOccurrences mapOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def sources
    (_face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Source → RootedAccountedUnfolding Source :=
  sourceOccurrences

def targets
    (_face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Target → RootedAccountedUnfolding Target :=
  targetOccurrences

def actualMap
    (_face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Source →ₗ[ℤ] Target :=
  mapOccurrence.root

def kernel
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Submodule ℤ Source :=
  LinearMap.ker face.actualMap

def range
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Submodule ℤ Target :=
  LinearMap.range face.actualMap

abbrev cokernel
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :=
  Target ⧸ face.range

/-- The degree-one carrier of the actual two-term presentation cofiber. -/
abbrev cofiber
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :=
  face.cokernel

/-- Every generated kernel defect retains its exact occurrence. -/
def kernelOccurrences
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence)
    (defect : face.kernel) : RootedAccountedUnfolding face.kernel :=
  RootedAccountedUnfolding.zero defect

/-- Every generated cofiber/cokernel defect retains its exact occurrence. -/
def cofiberOccurrences
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence)
    (defect : face.cofiber) : RootedAccountedUnfolding face.cofiber :=
  RootedAccountedUnfolding.zero defect

end RootGeneratedFiniteDefectPresentationAt

/-- Generated calculation receipt above the actual presentation.  Equal rank
and finite cokernel belong here rather than in the source face. -/
structure RootGeneratedFiniteDefectCalculationAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [Module.Free ℤ Source] [Module.Finite ℤ Source]
    [AddCommGroup Target] [Module.Free ℤ Target] [Module.Finite ℤ Target]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {sourceOccurrences : Source → RootedAccountedUnfolding Source}
    {targetOccurrences : Target → RootedAccountedUnfolding Target}
    {mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)}
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) : Prop where
  rank_eq : Module.finrank ℤ Source = Module.finrank ℤ Target
  cokernelFinite : Finite face.cokernel

namespace RootGeneratedFiniteDefectCalculationAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module.Free ℤ Source] [Module.Finite ℤ Source]
variable [AddCommGroup Target] [Module.Free ℤ Target] [Module.Finite ℤ Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)}
variable {face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
  sourceOccurrences targetOccurrences mapOccurrence}

theorem generate
    (rank_eq : Module.finrank ℤ Source = Module.finrank ℤ Target)
    (cokernelFinite : Finite face.cokernel) :
    RootGeneratedFiniteDefectCalculationAt face :=
  ⟨rank_eq, cokernelFinite⟩

end RootGeneratedFiniteDefectCalculationAt

/-- Realized finite-defect receipt. -/
structure RootGeneratedFiniteDefectReceiptAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [Module.Free ℤ Source] [Module.Finite ℤ Source]
    [AddCommGroup Target] [Module.Free ℤ Target] [Module.Finite ℤ Target]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {sourceOccurrences : Source → RootedAccountedUnfolding Source}
    {targetOccurrences : Target → RootedAccountedUnfolding Target}
    {mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)}
    (face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence)
    (calculation : RootGeneratedFiniteDefectCalculationAt face) : Type where
  private mk ::

namespace RootGeneratedFiniteDefectReceiptAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module.Free ℤ Source] [Module.Finite ℤ Source]
variable [AddCommGroup Target] [Module.Free ℤ Target] [Module.Finite ℤ Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →ₗ[ℤ] Target)}
variable {face : RootGeneratedFiniteDefectPresentationAt rootOccurrence
  sourceOccurrences targetOccurrences mapOccurrence}
variable {calculation : RootGeneratedFiniteDefectCalculationAt face}

def realize : RootGeneratedFiniteDefectReceiptAt face calculation :=
  ⟨⟩

theorem range_finrank_eq_target
    (_receipt : RootGeneratedFiniteDefectReceiptAt face calculation) :
    Module.finrank ℤ face.range = Module.finrank ℤ Target := by
  let _ : Finite face.cokernel := calculation.cokernelFinite
  exact (Submodule.finiteQuotient_iff face.range).mp inferInstance

/-- A finite cokernel between equal-rank free lattices forces the generated
kernel to vanish. -/
theorem kernel_eq_bot
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation) :
    face.kernel = ⊥ := by
  have source_finrank_le_range :
      Module.finrank ℤ Source ≤ Module.finrank ℤ face.range :=
    le_of_eq (calculation.rank_eq.trans receipt.range_finrank_eq_target.symm)
  have disjoint := Submodule.disjoint_ker_of_finrank_le
    (L := (⊤ : Submodule ℤ Source)) face.actualMap (by
      rw [Submodule.map_top]
      change Module.finrank ℤ (⊤ : Submodule ℤ Source) ≤
        Module.finrank ℤ face.range
      simpa only [finrank_top] using source_finrank_le_range)
  simpa [RootGeneratedFiniteDefectPresentationAt.kernel] using disjoint

theorem actualMap_injective
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation) :
    Function.Injective face.actualMap := by
  rw [← LinearMap.ker_eq_bot]
  exact receipt.kernel_eq_bot

/-- Canonical equivalence onto the actual generated range. -/
noncomputable def rangeEquiv
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation) :
    Source ≃ₗ[ℤ] face.range :=
  LinearEquiv.ofBijective face.actualMap.rangeRestrict
    ⟨by
      intro left right equality
      apply receipt.actualMap_injective
      exact congrArg Subtype.val equality,
    by
      intro target
      rcases target.property with ⟨source, source_eq⟩
      exact ⟨source, Subtype.ext source_eq⟩⟩

/-- Internal range basis generated from an installed source frame.  It is a
proof device and never becomes a producer field. -/
noncomputable def rangeBasis
    {Index : Type*}
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source) :
    Module.Basis Index ℤ face.range :=
  sourceBasis.map receipt.rangeEquiv

/-- Matrix readout installed only after independent source/target frames. -/
noncomputable def installedPresentationMatrix
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (_receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) :
    Matrix Index Index ℤ :=
  LinearMap.toMatrix sourceBasis targetBasis face.actualMap

/-- Determinant coordinate of the installed presentation frames. -/
noncomputable def installedDeterminantCoordinate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) : ℤ :=
  Matrix.det (receipt.installedPresentationMatrix sourceBasis targetBasis)

/-- The installed matrix determinant is the target-basis alternating
determinant of the actual source frame image. -/
theorem installedDeterminantCoordinate_eq_basisDet
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) :
    receipt.installedDeterminantCoordinate sourceBasis targetBasis =
      targetBasis.det (fun index => face.actualMap (sourceBasis index)) := by
  unfold installedDeterminantCoordinate installedPresentationMatrix
  rw [Module.Basis.det_apply]
  congr 1
  ext row column
  simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]

/-- Determinant/index law for the generated actual cokernel. -/
theorem natAbs_installedDeterminantCoordinate_eq_card_cokernel
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) :
    Int.natAbs
        (receipt.installedDeterminantCoordinate sourceBasis targetBasis) =
      Nat.card face.cokernel := by
  let _ : Finite face.cokernel := calculation.cokernelFinite
  change Int.natAbs
      (receipt.installedDeterminantCoordinate sourceBasis targetBasis) =
    Nat.card (Target ⧸ face.range)
  rw [receipt.installedDeterminantCoordinate_eq_basisDet]
  have cardinalityLaw := Submodule.natAbs_det_basis_change targetBasis
    face.range (receipt.rangeBasis sourceBasis)
  convert cardinalityLaw using 1
  congr 2

theorem card_kernel_eq_one
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation) :
    Nat.card face.kernel = 1 := by
  rw [receipt.kernel_eq_bot]
  exact Nat.card_unique

/-- Finite two-term homotopy cardinality keeps the generated cokernel and
kernel separate. -/
noncomputable def finiteHomotopyCardinality
    (_receipt : RootGeneratedFiniteDefectReceiptAt face calculation) : ℚ :=
  (Nat.card face.cokernel : ℚ) / (Nat.card face.kernel : ℚ)

/-- Exact finite-defect law in the equal-rank free-lattice regime. -/
theorem natAbs_determinant_eq_card_cokernel_div_card_kernel
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) :
    Int.natAbs
        (receipt.installedDeterminantCoordinate sourceBasis targetBasis) =
      Nat.card face.cokernel / Nat.card face.kernel := by
  rw [receipt.card_kernel_eq_one, Nat.div_one,
    receipt.natAbs_installedDeterminantCoordinate_eq_card_cokernel]

theorem finiteHomotopyCardinality_eq_natAbs_determinant
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (receipt : RootGeneratedFiniteDefectReceiptAt face calculation)
    (sourceBasis : Module.Basis Index ℤ Source)
    (targetBasis : Module.Basis Index ℤ Target) :
    receipt.finiteHomotopyCardinality =
      (Int.natAbs
        (receipt.installedDeterminantCoordinate sourceBasis targetBasis) : ℚ) := by
  unfold finiteHomotopyCardinality
  rw [receipt.card_kernel_eq_one, Nat.cast_one, div_one,
    receipt.natAbs_installedDeterminantCoordinate_eq_card_cokernel]

end RootGeneratedFiniteDefectReceiptAt

/-! ## Finite homology defects

Nontrivial finite kernels cannot occur in the equal-rank free-lattice map
above.  They occur after passing to actual finite homology carriers.  The
following companion face records that layer without pretending that a
torsion group itself has a rational determinant.
-/

/-- Root-owned map of actual finite homology carriers. -/
structure RootGeneratedFiniteHomologyMapAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [AddCommGroup Target]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (sourceOccurrences : Source → RootedAccountedUnfolding Source)
    (targetOccurrences : Target → RootedAccountedUnfolding Target)
    (mapOccurrence : RootedAccountedUnfolding (Source →+ Target)) : Type where
  private mk ::

namespace RootGeneratedFiniteHomologyMapAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [AddCommGroup Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →+ Target)}

def generate : RootGeneratedFiniteHomologyMapAt rootOccurrence
    sourceOccurrences targetOccurrences mapOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def actualMap
    (_face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    Source →+ Target :=
  mapOccurrence.root

def kernel
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    AddSubgroup Source :=
  face.actualMap.ker

def range
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :
    AddSubgroup Target :=
  face.actualMap.range

abbrev cokernel
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :=
  Target ⧸ face.range

abbrev cofiber
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence) :=
  face.cokernel

def kernelOccurrences
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence)
    (defect : face.kernel) : RootedAccountedUnfolding face.kernel :=
  RootedAccountedUnfolding.zero defect

def cofiberOccurrences
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence
      sourceOccurrences targetOccurrences mapOccurrence)
    (defect : face.cofiber) : RootedAccountedUnfolding face.cofiber :=
  RootedAccountedUnfolding.zero defect

end RootGeneratedFiniteHomologyMapAt

/-- Finiteness is generated by the actual homology calculation, not supplied
as a completed cardinality. -/
structure RootGeneratedFiniteHomologyCalculationAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [AddCommGroup Target]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {sourceOccurrences : Source → RootedAccountedUnfolding Source}
    {targetOccurrences : Target → RootedAccountedUnfolding Target}
    {mapOccurrence : RootedAccountedUnfolding (Source →+ Target)}
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence sourceOccurrences
      targetOccurrences mapOccurrence) : Prop where
  sourceFinite : Finite Source
  targetFinite : Finite Target

namespace RootGeneratedFiniteHomologyCalculationAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [AddCommGroup Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →+ Target)}
variable {face : RootGeneratedFiniteHomologyMapAt rootOccurrence
  sourceOccurrences targetOccurrences mapOccurrence}

theorem generate (sourceFinite : Finite Source)
    (targetFinite : Finite Target) :
    RootGeneratedFiniteHomologyCalculationAt face :=
  ⟨sourceFinite, targetFinite⟩

end RootGeneratedFiniteHomologyCalculationAt

structure RootGeneratedFiniteHomologyReceiptAt
    {Root : Type w} {Source : Type u} {Target : Type v}
    [AddCommGroup Source] [AddCommGroup Target]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {sourceOccurrences : Source → RootedAccountedUnfolding Source}
    {targetOccurrences : Target → RootedAccountedUnfolding Target}
    {mapOccurrence : RootedAccountedUnfolding (Source →+ Target)}
    (face : RootGeneratedFiniteHomologyMapAt rootOccurrence sourceOccurrences
      targetOccurrences mapOccurrence)
    (calculation : RootGeneratedFiniteHomologyCalculationAt face) : Type where
  private mk ::

namespace RootGeneratedFiniteHomologyReceiptAt

variable {Root : Type w} {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [AddCommGroup Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrences : Source → RootedAccountedUnfolding Source}
variable {targetOccurrences : Target → RootedAccountedUnfolding Target}
variable {mapOccurrence : RootedAccountedUnfolding (Source →+ Target)}
variable {face : RootGeneratedFiniteHomologyMapAt rootOccurrence
  sourceOccurrences targetOccurrences mapOccurrence}
variable {calculation : RootGeneratedFiniteHomologyCalculationAt face}

def realize : RootGeneratedFiniteHomologyReceiptAt face calculation :=
  ⟨⟩

/-- Exact finite kernel/cokernel cardinality balance for the actual homology
map. -/
theorem cardinality_balance
    (_receipt : RootGeneratedFiniteHomologyReceiptAt face calculation) :
    Nat.card Target * Nat.card face.kernel =
      Nat.card Source * Nat.card face.cokernel := by
  let _ : Finite Source := calculation.sourceFinite
  let _ : Finite Target := calculation.targetFinite
  have source_card :
      Nat.card Source = Nat.card face.range * Nat.card face.kernel := by
    unfold RootGeneratedFiniteHomologyMapAt.kernel
    unfold RootGeneratedFiniteHomologyMapAt.range
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        face.actualMap.ker,
      Nat.card_congr
        (QuotientAddGroup.quotientKerEquivRange face.actualMap).toEquiv]
  have target_card :
      Nat.card Target = Nat.card face.cokernel * Nat.card face.range := by
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup face.range
  calc
    Nat.card Target * Nat.card face.kernel =
        (Nat.card face.cokernel * Nat.card face.range) *
          Nat.card face.kernel := by rw [target_card]
    _ = (Nat.card face.range * Nat.card face.kernel) *
          Nat.card face.cokernel := by ac_rfl
    _ = Nat.card Source * Nat.card face.cokernel := by rw [← source_card]

/-- Finite homology cardinality shadow. -/
noncomputable def finiteHomotopyCardinality
    (_receipt : RootGeneratedFiniteHomologyReceiptAt face calculation) : ℚ :=
  (Nat.card face.cokernel : ℚ) / (Nat.card face.kernel : ℚ)

end RootGeneratedFiniteHomologyReceiptAt

end FiniteDefectDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
