import H0mework.Physics.JointSources.P712
import H0mework.Realization.Residual.P743

/-!
# Proposition 744: the first formula reaches the three producer nails

P743 proves the residual split first formula and its Hamiltonian/SAT energy
reading.  P710/P712 prove that the finite three-nail producer surface
(`alpha_s`, Yukawa depths, CKM/Jarlskog depth sum) is rigid: every accepted
package is the canonical shared Hamiltonian/SAT energy producer plus the
canonical finite physical output.

This file welds those two roots.  We strengthen the P710 surface by requiring
the package's own Hamiltonian/SAT energy producer `X.1` to obey the P743
face-local residual-split ledger.  Lean proves the strengthened surface is
still exactly the canonical package.  Thus the three finite producer nails are
not merely attached to the same carrier as the first formula; their accepted
shared energy producer is forced to read the same keep/trace residual split.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace GrandUnification

open ComplexityProjection
open AffineRelaxation

universe u v w z

/-! ## Producer packages whose energy readout obeys the first formula -/

/-- P710 plus the P743 residual-split energy ledger, checked against the
package's own Hamiltonian/SAT energy producer `X.1`. -/
def HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) : Prop :=
  HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
    (∀ face : GrandUnifiedProjectionFace, ∀ sigma : ℝ,
      ∀ S : SATPhaseFlowState Clause Var,
        X.1 (faceLocalHamiltonianSATResidualStep F face sigma S) +
            hamiltonianSATResidualWork S sigma =
          X.1 S) ∧
    (∀ face₂ face₁ _face₃ : GrandUnifiedProjectionFace, ∀ sigma1 sigma2 : ℝ,
      ∀ S : SATPhaseFlowState Clause Var,
        X.1
            (faceLocalHamiltonianSATResidualStep F face₂ sigma2
              (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) +
            hamiltonianSATResidualWork S (satOrField sigma1 sigma2) =
          X.1 S)

/-- THEOREM 1: adding the P743 residual-split ledger to the P710 three-nail
surface still leaves exactly the canonical package. -/
theorem
    hamiltonianSATCoordinateSpineProducerNailResidualSplitSurface_iff_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) :
    HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface F R X ↔
      X = canonicalHamiltonianSATPhysicalProducerPair Clause Var := by
  constructor
  · intro hX
    exact
      (hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical
        R X).1 hX.1
  · intro hX
    rw [hX]
    refine ⟨?_, ?_, ?_⟩
    · exact
        (hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical
          R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl
    · intro face sigma S
      change
        hamiltonianEnergyReadout
            (faceLocalHamiltonianSATResidualStep F face sigma S) +
            hamiltonianSATResidualWork S sigma =
          hamiltonianEnergyReadout S
      exact faceLocalHamiltonianSAT_energy_split_ledger F face sigma S
    · intro face₂ face₁ face₃ sigma1 sigma2 S
      change
        hamiltonianEnergyReadout
            (faceLocalHamiltonianSATResidualStep F face₂ sigma2
              (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) +
            hamiltonianSATResidualWork S (satOrField sigma1 sigma2) =
          hamiltonianEnergyReadout S
      exact faceLocalHamiltonianSAT_crossFace_energy_split_ledger
        F face₂ face₁ face₃ sigma1 sigma2 S

/-- THEOREM 2: every accepted P710 three-nail package automatically satisfies
the P743 residual-split energy ledger. -/
theorem
    hamiltonianSATCoordinateSpineProducerNailSurface_implies_residualSplitSurface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (hX : HamiltonianSATCoordinateSpineProducerNailSurface R X) :
    HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface F R X := by
  have hcanon :
      X = canonicalHamiltonianSATPhysicalProducerPair Clause Var :=
    (hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical
      R X).1 hX
  exact
    (hamiltonianSATCoordinateSpineProducerNailResidualSplitSurface_iff_canonical
      F R X).2 hcanon

/-- THEOREM 3: the residual-split strengthened surface still carries the three
finite producer nails. -/
theorem
    residualSplitProducerNailSurface_threeNails
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (hX : HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
      F R X) :
    X.2.2.axis = traceWeightedQCDPoincareCoordinateAxis ∧
      X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
      X.2.2.yukawaMassOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      X.2.2.ckmDepthSum = (386 : ℚ) := by
  have hcanon :
      X = canonicalHamiltonianSATPhysicalProducerPair Clause Var :=
    (hamiltonianSATCoordinateSpineProducerNailResidualSplitSurface_iff_canonical
      F R X).1 hX
  rw [hcanon]
  exact ⟨canonicalFiniteOutput_axis_eq_traceWeightedCoordinateAxis,
    rfl, rfl, rfl⟩

/-! ## Packaged certificate -/

/-- P744 certificate: accepted three-nail producer packages are exactly those
whose shared Hamiltonian/SAT energy producer is the P743 residual-split readout. -/
structure ResidualSplitThreeNailProducerBridgeCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] where
  first_formula :
    ResidualSplitFirstFormulaCertificate.{v, w, v}
  three_nail_root :
    HamiltonianSATCoordinateSpineThreeNailReadoutRootCertificate.{u, v, w, z}
      E Clause Var
  residual_split_surface_iff_canonical :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
              F R X ↔
            X = canonicalHamiltonianSATPhysicalProducerPair Clause Var
  p710_surface_implies_residual_split :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailSurface R X ->
            HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
              F R X
  residual_split_surface_three_nails :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
              F R X ->
            X.2.2.axis = traceWeightedQCDPoincareCoordinateAxis ∧
              X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
              X.2.2.yukawaMassOrder =
                [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              X.2.2.ckmDepthSum = (386 : ℚ)

/-- THEOREM 4: the residual-split first formula reaches the finite three-nail
producer surface. -/
def residualSplitThreeNailProducerBridgeCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause] :
    ResidualSplitThreeNailProducerBridgeCertificate E Clause Var where
  first_formula := residualSplitFirstFormulaCertificate
  three_nail_root :=
    hamiltonianSATCoordinateSpineThreeNailReadoutRootCertificate
      (E := E) (Clause := Clause) (Var := Var)
  residual_split_surface_iff_canonical := by
    intro F R X
    exact
      hamiltonianSATCoordinateSpineProducerNailResidualSplitSurface_iff_canonical
        F R X
  p710_surface_implies_residual_split := by
    intro F R X hX
    exact
      hamiltonianSATCoordinateSpineProducerNailSurface_implies_residualSplitSurface
        F R X hX
  residual_split_surface_three_nails := by
    intro F R X hX
    exact residualSplitProducerNailSurface_threeNails F R X hX

end GrandUnification
end SaturationMonoid
