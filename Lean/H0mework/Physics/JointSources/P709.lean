import H0mework.Physics.RunningSources.P708

/-!
# Proposition 709: the active-source coordinate package is the four-face formula

P708 is the strongest finite producer root so far: it welds the
Hamiltonian/SAT same-carrier energy package, the running-σ coordinate-action
spine, and the finite `alpha_s` singleton active-source normal form.

This file closes the remaining *readout* gap.  It makes explicit that the same
P708 package's finite output is not merely a physical-output coordinate: it is
the canonical P701/P702 Energy/Information/Mathematics/Physics diagonal
readout.  Thus the slogan

`Energy = Information = Mathematics = Physics`

is now read directly from the active-source coordinate-spine package rather
than only by following the internal P705/P706 field path.

Boundary: this is still the finite source-law / active-source carrier.  It
does not derive smooth SU(7) threshold dynamics, universal QFT loop weights,
three-loop RG, Higgs spectra, arbitrary physical Hamiltonians, Goldbach/RH,
polynomial SAT, or `P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open ComplexityProjection
open StandardModelConstraint

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## The P708 package as a four-face formula surface -/

/-- The P708 active-source coordinate-spine package, strengthened with an
explicit P701/P702 four-face diagonal readout obligation on the same output
coordinate.  The obligation is redundant but useful as a front-door formula
surface. -/
def HamiltonianSATCoordinateSpineUnifiedFormulaSurface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) : Prop :=
  HamiltonianSATCoordinateSpineActiveSourceSurface R X ∧
    EnergyInformationMathematicsPhysicsDiagonalSurface X.2.2

/-- THEOREM 1: adding the explicit four-face formula readout still leaves
exactly the canonical P708 package. -/
theorem hamiltonianSATCoordinateSpineUnifiedFormulaSurface_iff_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) :
    HamiltonianSATCoordinateSpineUnifiedFormulaSurface R X ↔
      X = canonicalHamiltonianSATPhysicalProducerPair Clause Var := by
  constructor
  · intro hX
    exact
      (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
        R X).1 hX.1
  · intro hX
    rw [hX]
    refine ⟨?_, ?_⟩
    · exact
        (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
          R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl
    · exact
        (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
          canonicalSourceLawFinitePhysicalOutput).2 rfl

/-- The subtype of accepted active-source coordinate-spine packages with an
explicit four-face formula readout. -/
def HamiltonianSATCoordinateSpineUnifiedFormulaSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    Type (max v w) :=
  { X : HamiltonianSATPhysicalProducerPair Clause Var //
    HamiltonianSATCoordinateSpineUnifiedFormulaSurface R X }

/-- The canonical unified-formula package. -/
def canonicalHamiltonianSATCoordinateSpineUnifiedFormulaSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATCoordinateSpineUnifiedFormulaSubtype Clause Var R :=
  ⟨canonicalHamiltonianSATPhysicalProducerPair Clause Var,
    (hamiltonianSATCoordinateSpineUnifiedFormulaSurface_iff_canonical
      R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl⟩

/-- THEOREM 2: every unified-formula package is canonical. -/
theorem hamiltonianSATCoordinateSpineUnifiedFormulaSubtype_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineUnifiedFormulaSubtype Clause Var R) :
    X =
      canonicalHamiltonianSATCoordinateSpineUnifiedFormulaSubtype
        Clause Var R := by
  cases X with
  | mk X hX =>
      apply Subtype.ext
      exact
        (hamiltonianSATCoordinateSpineUnifiedFormulaSurface_iff_canonical
          R X).1 hX

/-- THEOREM 3: the unified-formula package subtype is equivalent to `Unit`. -/
def hamiltonianSATCoordinateSpineUnifiedFormulaSubtypeEquivUnit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATCoordinateSpineUnifiedFormulaSubtype Clause Var R ≃ Unit where
  toFun _ := ()
  invFun _ :=
    canonicalHamiltonianSATCoordinateSpineUnifiedFormulaSubtype Clause Var R
  left_inv := by
    intro X
    exact
      (hamiltonianSATCoordinateSpineUnifiedFormulaSubtype_eq_canonical
        R X).symm
  right_inv := by
    intro x
    cases x
    rfl

/-! ## Projection from the P708 package to the P701/P702 diagonal -/

/-- The output projection from an accepted P708 package to the P701/P702
four-face diagonal subtype. -/
def activeSourcePackageOutputDiagonalSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R) :
    EnergyInformationMathematicsPhysicsDiagonalSubtype :=
  ⟨X.1.2.2, by
    have hcanon :
        X.1 = canonicalHamiltonianSATPhysicalProducerPair Clause Var :=
      (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
        R X.1).1 X.2
    rw [hcanon]
    exact
      (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
        canonicalSourceLawFinitePhysicalOutput).2 rfl⟩

/-- THEOREM 4: every accepted P708 package projects to the canonical
four-face diagonal subtype. -/
theorem activeSourcePackageOutputDiagonalSubtype_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R) :
    activeSourcePackageOutputDiagonalSubtype R X =
      canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype :=
  energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical
    (activeSourcePackageOutputDiagonalSubtype R X)

/-- THEOREM 5: the finite output of every accepted P708 package is the
canonical source-law output. -/
theorem activeSourcePackageOutput_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R) :
    X.1.2.2 = canonicalSourceLawFinitePhysicalOutput := by
  have hcanon :
      X.1 = canonicalHamiltonianSATPhysicalProducerPair Clause Var :=
    (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
      R X.1).1 X.2
  rw [hcanon]
  rfl

/-- THEOREM 6: the finite output of every accepted P708 package lies on every
Energy/Information/Mathematics/Physics face. -/
theorem activeSourcePackageOutput_on_face
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R)
    (face : EnergyInformationMathematicsPhysicsFace) :
    EnergyInformationMathematicsPhysicsFaceSurface face X.1.2.2 := by
  rw [activeSourcePackageOutput_eq_canonical R X]
  exact canonicalSourceLawFinitePhysicalOutput_on_face face

/-! ## Packaged root certificate -/

/-- P709 root: P708's active-source coordinate-spine producer package is also
the explicit P701/P702 four-face unified-formula package. -/
structure HamiltonianSATCoordinateSpineUnifiedFormulaRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] where
  p708_root :
    HamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
      E Clause Var
  p702_diagonal_no_family :
    EnergyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate.{z, u, v, w}
      E
  formula_surface_iff_canonical :
    ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
      HamiltonianSATCoordinateSpineUnifiedFormulaSurface.{u, v, w, z}
        p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root
        X ↔
        X = canonicalHamiltonianSATPhysicalProducerPair Clause Var
  formula_subtype_equiv_unit :
    HamiltonianSATCoordinateSpineUnifiedFormulaSubtype.{u, v, w, z}
      Clause Var
      p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root ≃
        Unit
  p708_output_to_diagonal :
    ∀ X : HamiltonianSATCoordinateSpineActiveSourceSubtype.{u, v, w, z}
      Clause Var
      p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root,
      activeSourcePackageOutputDiagonalSubtype
        p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root
        X =
          canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype
  p708_output_eq_canonical :
    ∀ X : HamiltonianSATCoordinateSpineActiveSourceSubtype.{u, v, w, z}
      Clause Var
      p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root,
      X.1.2.2 = canonicalSourceLawFinitePhysicalOutput
  p708_output_on_every_face :
    ∀ (X : HamiltonianSATCoordinateSpineActiveSourceSubtype.{u, v, w, z}
      Clause Var
      p708_root.p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
      (face : EnergyInformationMathematicsPhysicsFace),
      EnergyInformationMathematicsPhysicsFaceSurface face X.1.2.2
  active_source_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
        s = .su7Breaking

/-- THEOREM 7: the P709 unified-formula root is inhabited. -/
def hamiltonianSATCoordinateSpineUnifiedFormulaRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    HamiltonianSATCoordinateSpineUnifiedFormulaRootCertificate
      E Clause Var where
  p708_root :=
    hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
      (E := E) Clause Var
  p702_diagonal_no_family :=
    energyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate
      (E := E)
  formula_surface_iff_canonical := by
    intro X
    exact
      hamiltonianSATCoordinateSpineUnifiedFormulaSurface_iff_canonical
        ((hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
          (E := E) Clause Var).p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
        X
  formula_subtype_equiv_unit :=
    hamiltonianSATCoordinateSpineUnifiedFormulaSubtypeEquivUnit Clause Var
      ((hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
        (E := E) Clause Var).p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
  p708_output_to_diagonal := by
    intro X
    exact
      activeSourcePackageOutputDiagonalSubtype_eq_canonical
        ((hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
          (E := E) Clause Var).p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
        X
  p708_output_eq_canonical := by
    intro X
    exact
      activeSourcePackageOutput_eq_canonical
        ((hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
          (E := E) Clause Var).p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
        X
  p708_output_on_every_face := by
    intro X face
    exact
      activeSourcePackageOutput_on_face
        ((hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate.{u, v, w, z}
          (E := E) Clause Var).p707_root.p706_root.p705_full_diagonal_root.p703_grand_root)
        X face
  active_source_iff_su7 :=
    alphaStrongQCDPoincareUnifiedAxis_activeSource_iff_su7Breaking

end GrandUnification
end SaturationMonoid
