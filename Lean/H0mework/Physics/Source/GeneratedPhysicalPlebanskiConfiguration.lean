import H0mework.Physics.Jets.JetLocalPhysicalPlebanskiAction

/-!
# Source-generated physical Plebanski configuration

The proof-free anholonomic source independently generates a torsion-free spin
connection value and a coframe two-jet curvature.  This module reconstructs an
antisymmetric connection derivative jet from those outputs and proves that
its genuine non-Abelian curvature `dω+ω∧ω` is exactly the generated
Lorentz curvature.

It then forms the jet-local action configuration and proves, in separate
layers, coframe nondegeneracy, torsion freedom, physical `II+` simplicity, and
curvature provenance.  Full `deltaB/deltaOmega/deltaE` stationarity remains an
open equation; no stationary certificate is stored or claimed here.
-/

namespace SaturationMonoid.PhysicsCore.SourceGeneratedPhysicalPlebanskiConfiguration

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction

noncomputable section

def sourceOmegaValue (source : Source) : OmegaValue :=
  WithLp.toLp 2 fun index =>
    (source.geometryAtOrigin).spin.spinConnection
      index.1 index.2.1 index.2.2

def sourceOmegaBracket
    (source : Source)
    (first second internalOut internalIn : LorentzianIndex) : ℝ :=
  ∑ middle,
    ((source.geometryAtOrigin).spin.spinConnection
        first internalOut middle *
      (source.geometryAtOrigin).spin.spinConnection
        second middle internalIn -
    (source.geometryAtOrigin).spin.spinConnection
        second internalOut middle *
      (source.geometryAtOrigin).spin.spinConnection
        first middle internalIn)

theorem sourceOmegaBracket_antisymm
    (source : Source)
    (first second internalOut internalIn : LorentzianIndex) :
    sourceOmegaBracket source second first internalOut internalIn =
      -sourceOmegaBracket source first second internalOut internalIn := by
  unfold sourceOmegaBracket
  have hsum :
      (∑ middle,
        ((source.geometryAtOrigin).spin.spinConnection
            second internalOut middle *
          (source.geometryAtOrigin).spin.spinConnection
            first middle internalIn -
        (source.geometryAtOrigin).spin.spinConnection
            first internalOut middle *
          (source.geometryAtOrigin).spin.spinConnection
            second middle internalIn)) =
        -∑ middle,
          ((source.geometryAtOrigin).spin.spinConnection
              first internalOut middle *
            (source.geometryAtOrigin).spin.spinConnection
              second middle internalIn -
          (source.geometryAtOrigin).spin.spinConnection
              second internalOut middle *
            (source.geometryAtOrigin).spin.spinConnection
              first middle internalIn) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro middle _
    ring
  exact hsum

/-- Antisymmetric derivative jet reconstructed from the independently
generated coframe curvature and the generated spin-connection value. -/
def sourceOmegaDerivative (source : Source) : OmegaDerivative :=
  WithLp.toLp 2 fun index =>
    let derivativeDirection := index.1
    let formDirection := index.2.1
    let internalOut := index.2.2.1
    let internalIn := index.2.2.2
    (source.coordinateCurvatureAtOrigin
          internalOut internalIn derivativeDirection formDirection -
        sourceOmegaBracket source derivativeDirection formDirection
          internalOut internalIn) / 2

def sourceConnectionJet (source : Source) : ConnectionJet :=
  (sourceOmegaValue source, sourceOmegaDerivative source)

def sourceCurvatureVector (source : Source) : BivectorVector :=
  vectorOfPhysicalBivector source.lorentzCurvatureAtOrigin

theorem nonAbelianCurvature_sourceConnectionJet (source : Source) :
    nonAbelianCurvature (sourceConnectionJet source) =
      sourceCurvatureVector source := by
  ext pair
  let internalPair := pair.1
  let spacetimePair := pair.2
  let internalOut := pairFirst internalPair
  let internalIn := pairSecond internalPair
  let first := pairFirst spacetimePair
  let second := pairSecond spacetimePair
  have hcurvature :=
    source.coordinateCurvatureAtOrigin_antisymm
      internalOut internalIn first second
  have hbracket :=
    sourceOmegaBracket_antisymm source first second internalOut internalIn
  simp only [nonAbelianCurvature, sourceConnectionJet, sourceOmegaValue,
    sourceOmegaDerivative, omegaDerivative, omegaValue,
    sourceCurvatureVector, vectorOfPhysicalBivector,
    Source.lorentzCurvatureAtOrigin]
  change
    minkowskiInternalSign internalOut *
      (((source.coordinateCurvatureAtOrigin
            internalOut internalIn first second -
          sourceOmegaBracket source first second internalOut internalIn) / 2) -
        ((source.coordinateCurvatureAtOrigin
            internalOut internalIn second first -
          sourceOmegaBracket source second first internalOut internalIn) / 2) +
        sourceOmegaBracket source first second internalOut internalIn) =
      minkowskiInternalSign internalOut *
        source.coordinateCurvatureAtOrigin
          internalOut internalIn first second
  rw [hcurvature, hbracket]
  ring

def tetradVectorAtOrigin (source : Source) : TetradVector :=
  WithLp.toLp 2 fun pair => (source.jetAt 0).coframe pair.1 pair.2

def sourceBivectorAtOrigin (source : Source) : BivectorVector :=
  physicalIIPlusMap (tetradVectorAtOrigin source)

def sourceActionConfiguration (source : Source) : Configuration where
  connection := sourceConnectionJet source
  bivector := sourceBivectorAtOrigin source
  multiplier := 0
  tetrad := tetradVectorAtOrigin source

theorem sourceActionConfiguration_simplicity (source : Source) :
    deltaPhi (sourceActionConfiguration source) = 0 := by
  apply (deltaPhi_eq_zero_iff_physicalIIPlus
    (sourceActionConfiguration source)).mpr
  rfl

theorem sourceActionConfiguration_tetrad_nondegenerate (source : Source) :
    Matrix.det (coframeOfTetradVector
      (sourceActionConfiguration source).tetrad) ≠ 0 := by
  have hcoframe :
      coframeOfTetradVector (sourceActionConfiguration source).tetrad =
        (source.jetAt 0).coframe := by
    rfl
  rw [hcoframe]
  exact source.jetAt_zero_nondegenerate

theorem sourceActionConfiguration_torsionFree (source : Source) :
    PointwiseLorentzianCoframeJet.TorsionFree
      (source.geometryAtOrigin).spin.affineConnection :=
  (source.geometryAtOrigin).spin.affineTorsionFree

theorem sourceActionConfiguration_curvature_generated (source : Source) :
    nonAbelianCurvature (sourceActionConfiguration source).connection =
      sourceCurvatureVector source :=
  nonAbelianCurvature_sourceConnectionJet source

theorem positiveSource_action_curvature_nonzero_component :
    nonAbelianCurvature
        (sourceActionConfiguration positiveSource).connection (0, 0) =
      (1 / 4 : ℝ) := by
  rw [sourceActionConfiguration_curvature_generated]
  norm_num [sourceCurvatureVector, vectorOfPhysicalBivector,
    Source.lorentzCurvatureAtOrigin, pairFirst, pairSecond,
    minkowskiInternalSign,
    ProofFreeRicherAnholonomicSource.positiveSource_curvature_nonzero_component]

/-- Explicit layered source result before the still-open full stationarity
equations. -/
theorem proofFreeSource_generates_physicalActionConfiguration
    (source : Source) :
    Matrix.det (coframeOfTetradVector
        (sourceActionConfiguration source).tetrad) ≠ 0 ∧
      PointwiseLorentzianCoframeJet.TorsionFree
        (source.geometryAtOrigin).spin.affineConnection ∧
      deltaPhi (sourceActionConfiguration source) = 0 ∧
      nonAbelianCurvature (sourceActionConfiguration source).connection =
        sourceCurvatureVector source :=
  ⟨sourceActionConfiguration_tetrad_nondegenerate source,
    sourceActionConfiguration_torsionFree source,
    sourceActionConfiguration_simplicity source,
    sourceActionConfiguration_curvature_generated source⟩

end
end SaturationMonoid.PhysicsCore.SourceGeneratedPhysicalPlebanskiConfiguration
