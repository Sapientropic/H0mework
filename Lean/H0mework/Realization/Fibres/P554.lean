import Mathlib.Topology.MetricSpace.Isometry
import H0mework.Realization.Fibres.P553

/-!
# Proposition 554: sigma-zero relaxed fibers preserve metric structure

P550 proved that the sigma-zero fiber is homeomorphic to the standard carrier.
This file strengthens the metric face: whenever the carrier has a
`MetricSpace`, the zero fiber carries the induced metric along the forgetful
map, and that forgetful map is an `IsometryEquiv`.

Thus the metric-space object is also a genuine zero-fiber specialization:
distances on `X_0` are definitionally the distances of the corresponding
standard points in `X`.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic metric transfer -/

/-- The metric on the sigma-zero fiber induced by the forgetful map to the
standard carrier. -/
@[reducible] def sigmaZeroRelaxedMetricSpaceInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] :
    MetricSpace (SigmaRelaxedObject K X H (0 : K)) :=
  MetricSpace.induced
    (sigmaZeroForget (K := K) (X := X) (H := H))
    (sigmaZeroRelaxedEquiv K X H).injective inferInstance

/-- THEOREM 1: zero-fiber distance is exactly carrier distance after
forgetting headroom. -/
@[simp] theorem sigmaZeroRelaxed_dist_eq
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X]
    (a b : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedMetricSpaceInst K X H
    dist a b =
      dist
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
        (sigmaZeroForget (K := K) (X := X) (H := H) b) :=
  rfl

/-- THEOREM 2: the sigma-zero forgetful map is an isometry. -/
theorem sigmaZeroForget_isometry
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] :
    letI := sigmaZeroRelaxedMetricSpaceInst K X H
    Isometry (sigmaZeroForget (K := K) (X := X) (H := H)) := by
  intro a b
  rfl

/-- THEOREM 3: the sigma-zero fiber is isometric to its standard carrier. -/
def sigmaZeroRelaxedIsometryEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] : by
      letI := sigmaZeroRelaxedMetricSpaceInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃ᵢ X := by
  letI := sigmaZeroRelaxedMetricSpaceInst K X H
  exact
    { toEquiv := sigmaZeroRelaxedEquiv K X H
      isometry_toFun := sigmaZeroForget_isometry K X H }

@[simp] theorem sigmaZeroRelaxedIsometryEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedMetricSpaceInst K X H
    sigmaZeroRelaxedIsometryEquiv K X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

/-- Compact generic metric certificate for the sigma-zero fiber. -/
structure SigmaZeroRelaxedMetricCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] where
  metric_inst :
    MetricSpace (SigmaRelaxedObject K X H (0 : K))
  isometry_equiv :
    letI := metric_inst
    SigmaRelaxedObject K X H (0 : K) ≃ᵢ X
  dist_eq :
    letI := metric_inst
    ∀ a b : SigmaRelaxedObject K X H (0 : K),
      dist a b =
        dist
          (sigmaZeroForget (K := K) (X := X) (H := H) a)
          (sigmaZeroForget (K := K) (X := X) (H := H) b)

/-- THEOREM 4: the generic metric certificate is inhabited. -/
def sigmaZeroRelaxedMetricCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] :
    SigmaZeroRelaxedMetricCertificate K X H where
  metric_inst := sigmaZeroRelaxedMetricSpaceInst K X H
  isometry_equiv := by
    letI := sigmaZeroRelaxedMetricSpaceInst K X H
    exact sigmaZeroRelaxedIsometryEquiv K X H
  dist_eq := by
    intro a b
    rfl

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object metric table -/

/-- Transported metric on any metric-valued core-object zero fiber. -/
@[reducible] def coreObjectSigmaZeroMetricSpaceInst
    (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)] :
    MetricSpace (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedMetricSpaceInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 5: every metric-valued core object's zero fiber is isometric to
its standard carrier. -/
def coreObjectSigmaZeroIsometryEquiv
    (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroMetricSpaceInst O
      exact CoreObjectSigmaZeroFiber O ≃ᵢ CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroMetricSpaceInst O
  exact sigmaZeroRelaxedIsometryEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZero_dist_eq
    (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)]
    (a b : CoreObjectSigmaZeroFiber O) :
    letI := coreObjectSigmaZeroMetricSpaceInst O
    dist a b =
      dist (coreObjectSigmaZeroForget O a) (coreObjectSigmaZeroForget O b) :=
  rfl

@[simp] theorem coreObjectSigmaZeroIsometryEquiv_apply
    (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)]
    (z : CoreObjectSigmaZeroFiber O) :
    letI := coreObjectSigmaZeroMetricSpaceInst O
    coreObjectSigmaZeroIsometryEquiv O z =
      coreObjectSigmaZeroForget O z :=
  rfl

/-- Table certificate: every metric-valued core carrier has an isometric
sigma-zero fiber. -/
structure CoreObjectSigmaZeroMetricTableCertificate where
  group_level_table :
    CoreObjectSigmaZeroGroupLevelTableCertificate
  metric_inst :
    ∀ (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)],
      MetricSpace (CoreObjectSigmaZeroFiber O)
  isometry_equiv :
    ∀ (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroMetricSpaceInst O
      CoreObjectSigmaZeroFiber O ≃ᵢ CoreObjectCarrier O
  dist_eq :
    ∀ (O : CoreMathematicalObject18) [MetricSpace (CoreObjectCarrier O)]
      (a b : CoreObjectSigmaZeroFiber O),
      letI := coreObjectSigmaZeroMetricSpaceInst O
      dist a b =
        dist (coreObjectSigmaZeroForget O a) (coreObjectSigmaZeroForget O b)

/-- THEOREM 6: the core-object metric table is inhabited. -/
def coreObjectSigmaZeroMetricTableCertificate :
    CoreObjectSigmaZeroMetricTableCertificate where
  group_level_table := coreObjectSigmaZeroGroupLevelTableCertificate
  metric_inst := by
    intro O _inst
    exact coreObjectSigmaZeroMetricSpaceInst O
  isometry_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroIsometryEquiv O
  dist_eq := by
    intro O _inst a b
    rfl

end SaturationMonoid
