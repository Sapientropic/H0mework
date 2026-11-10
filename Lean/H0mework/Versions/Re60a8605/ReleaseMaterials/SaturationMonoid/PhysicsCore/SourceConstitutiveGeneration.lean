import Mathlib

/-!
# Upstream source-side constitutive generation

This module deliberately does not import `ConstitutiveHardGate`, a target
gauge block, or any terminal Euler--Lagrange residual.  It fixes one
equality-valued packaging relation upstream: a generated-law record is
definitionally assembled from the abstract tetrad, induced-metric, coupling,
and internal-constitutive readouts already carried by the interface.  A
downstream neutral geometry adapter applies a metric-to-Hodge construction;
this module cannot see that target.

The construction is still an abstract source-geometry interface, not a
concrete SU(7) physical producer.  Its purpose is to prevent downstream code
from supplying an arbitrary `generatedBySource` predicate after seeing the
hard-gate target.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uScalar uSource uTetrad uMetric uInternal

/-- Abstract packaging of the constitutive fields supplied by a source-side
interface.  It stores a spacetime metric, not a caller-supplied Hodge map or a
terminal gauge block.  This structure does not itself derive any field from
more primitive physical coordinates. -/
structure SourceGeneratedConstitutiveLaw
    (Scalar : Type uScalar) (Metric : Type uMetric)
    (InternalConstitutive : Type uInternal) [Field Scalar] where
  spacetimeMetric : Metric
  strongCouplingSquared : Scalarˣ
  weakCouplingSquared : Scalarˣ
  hyperchargeCouplingSquared : Scalarˣ
  internalConstitutive : InternalConstitutive

/-- Abstract upstream source geometry.  The downstream stage-two adapter
chooses the Plebanski `II+` sector by restricting the configuration domain to
the bivector constructed from `tetradOf χ`.  It does not claim that the
unconstrained Plebanski equations eliminate the other three sectors. -/
structure SourceMetricConstitutiveGeometry
    (Source : Type uSource) (Scalar : Type uScalar)
    (Tetrad : Type uTetrad) (Metric : Type uMetric)
    (InternalConstitutive : Type uInternal) [Field Scalar] where
  admissible : Source → Prop
  tetradOf : Source → Tetrad
  metricOfTetrad : Tetrad → Metric
  strongCouplingSquaredOf : Source → Scalarˣ
  weakCouplingSquaredOf : Source → Scalarˣ
  hyperchargeCouplingSquaredOf : Source → Scalarˣ
  internalConstitutiveOf : Source → InternalConstitutive

namespace SourceMetricConstitutiveGeometry

variable {Source : Type uSource} {Scalar : Type uScalar}
variable {Tetrad : Type uTetrad}
variable {Metric : Type uMetric} {InternalConstitutive : Type uInternal}
variable [Field Scalar]

/-- Deterministic packaging/readout of the functions already carried by `G`.
It is not, by itself, a physical producer theorem. -/
def generatedLaw
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (χ : Source) :
    SourceGeneratedConstitutiveLaw Scalar Metric InternalConstitutive where
  spacetimeMetric := G.metricOfTetrad (G.tetradOf χ)
  strongCouplingSquared := G.strongCouplingSquaredOf χ
  weakCouplingSquared := G.weakCouplingSquaredOf χ
  hyperchargeCouplingSquared := G.hyperchargeCouplingSquaredOf χ
  internalConstitutive := G.internalConstitutiveOf χ

/-- The fixed upstream generation relation.  Downstream callers cannot replace
it by `True` without changing this source module. -/
def GeneratedBySource
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (χ : Source)
    (law : SourceGeneratedConstitutiveLaw Scalar Metric
      InternalConstitutive) : Prop :=
  law = G.generatedLaw χ

theorem generatedLaw_isGenerated
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (χ : Source) :
    G.GeneratedBySource χ (G.generatedLaw χ) :=
  rfl

theorem generatedBySource_unique
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (χ : Source)
    (law : SourceGeneratedConstitutiveLaw Scalar Metric InternalConstitutive)
    (hgenerated : G.GeneratedBySource χ law) :
    law = G.generatedLaw χ :=
  hgenerated

/-- The generated metric is definitionally the metric of the source tetrad.
The downstream adapter, not this upstream module, applies a metric-to-Hodge
construction to both sides. -/
@[simp]
theorem generatedLaw_metric_eq_metricOfTetrad
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (χ : Source) :
    (G.generatedLaw χ).spacetimeMetric =
      G.metricOfTetrad (G.tetradOf χ) :=
  rfl

end SourceMetricConstitutiveGeometry

end PhysicsCore
end SaturationMonoid
