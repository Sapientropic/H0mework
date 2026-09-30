import H0mework.Realization.Residual.PathTransport

/-!
# Products of path-indexed residual transports

Two residual transports over the same native quiver can be retained on the
product carrier without merging their responsibilities.  The edge keep,
actual update law, path trace, and recollectable write-back are all formed
componentwise.  The two coordinate projections are concrete transport
morphisms, so their path and write-back naturality follows from the common
source path rather than from a same-event naming convention.

This is a transporter/formation module.  It does not assert that either
projection is faithful on every trace, generate a discrete gap, or provide a
target obstruction consumer.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

universe uK uE uF uV uQ

namespace PathIndexedResidualTransport

variable {K : Type uK} {E : Type uE} {F : Type uF}
variable {Vertex : Type uV}
variable [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup F] [Module K F]
variable [Quiver.{uQ} Vertex]

/-- Componentwise keep on a product residual carrier. -/
def productKeep
    (leftKeep : E →ₗ[K] E)
    (rightKeep : F →ₗ[K] F) :
    (E × F) →ₗ[K] (E × F) where
  toFun residual :=
    (leftKeep residual.1, rightKeep residual.2)
  map_add' := by
    intro left right
    simp
  map_smul' := by
    intro scalar residual
    simp

@[simp] theorem productKeep_apply
    (leftKeep : E →ₗ[K] E)
    (rightKeep : F →ₗ[K] F)
    (residual : E × F) :
    productKeep leftKeep rightKeep residual =
      (leftKeep residual.1, rightKeep residual.2) := by
  rfl

/-- Product formation for two transports sharing the same native path. -/
def product
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex) :
    PathIndexedResidualTransport K (E × F) Vertex where
  residual vertex :=
    (left.residual vertex, right.residual vertex)
  edgeKeep edge :=
    productKeep (left.edgeKeep edge) (right.edgeKeep edge)
  edge_residual_transport := by
    intro source target edge
    apply Prod.ext
    · exact left.edge_residual_transport edge
    · exact right.edge_residual_transport edge

@[simp] theorem product_residual_apply
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    (vertex : Vertex) :
    (left.product right).residual vertex =
      (left.residual vertex, right.residual vertex) := by
  rfl

@[simp] theorem product_edgeKeep_apply
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (edge : source ⟶ target)
    (residual : E × F) :
    (left.product right).edgeKeep edge residual =
      (left.edgeKeep edge residual.1,
        right.edgeKeep edge residual.2) := by
  rfl

/-- Product path keeps remain componentwise along the entire common path. -/
@[simp] theorem product_pathKeep_apply
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target)
    (residual : E × F) :
    (left.product right).pathKeep path residual =
      (left.pathKeep path residual.1,
        right.pathKeep path residual.2) := by
  induction path with
  | nil =>
      rfl
  | cons path edge inductionHypothesis =>
      change
        (left.edgeKeep edge
            ((left.product right).pathKeep path residual).1,
          right.edgeKeep edge
            ((left.product right).pathKeep path residual).2) =
          (left.edgeKeep edge (left.pathKeep path residual.1),
            right.edgeKeep edge (right.pathKeep path residual.2))
      rw [inductionHypothesis]

/-- Forced trace formation commutes with the common path on every carrier
input, before specializing to the actual source residual. -/
theorem product_pathTraceAt_eq
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target)
    (residual : E × F) :
    (left.product right).pathTraceAt path residual =
      (left.pathTraceAt path residual.1,
        right.pathTraceAt path residual.2) := by
  rw [pathTraceAt, pathTraceAt, pathTraceAt]
  simp only [AffineRelaxation.linearResidualTrace,
    product_pathKeep_apply]
  rfl

/-- The actual product trace retains both component traces without summing
or diagonalizing them. -/
theorem product_pathTrace_eq
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    (left.product right).pathTrace path =
      (left.pathTrace path, right.pathTrace path) := by
  rw [pathTrace, pathTrace, pathTrace]
  exact left.product_pathTraceAt_eq right path
    (left.residual source, right.residual source)

/-- A product trace is zero exactly when both retained responsibilities are
zero. -/
theorem product_pathTrace_eq_zero_iff
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    (left.product right).pathTrace path = 0 ↔
      left.pathTrace path = 0 ∧ right.pathTrace path = 0 := by
  rw [left.product_pathTrace_eq right path]
  simp

/-- Left coordinate projection on a product residual carrier. -/
def productFst : (E × F) →ₗ[K] E where
  toFun := Prod.fst
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar residual
    rfl

/-- Right coordinate projection on a product residual carrier. -/
def productSnd : (E × F) →ₗ[K] F where
  toFun := Prod.snd
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar residual
    rfl

/-- The first coordinate is a concrete path-transport morphism. -/
def productFstMorphism
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex) :
    Morphism (left.product right) left where
  quiverMap := Prefunctor.id Vertex
  carrierMap := productFst
  residual_naturality := by
    intro vertex
    rfl
  edge_keep_naturality := by
    intro source target edge residual
    rfl

/-- The second coordinate is a concrete path-transport morphism. -/
def productSndMorphism
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex) :
    Morphism (left.product right) right where
  quiverMap := Prefunctor.id Vertex
  carrierMap := productSnd
  residual_naturality := by
    intro vertex
    rfl
  edge_keep_naturality := by
    intro source target edge residual
    rfl

theorem productFstMorphism_mapPath_eq
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    (left.productFstMorphism right).mapPath path = path := by
  change (Prefunctor.id Vertex).mapPath path = path
  exact Prefunctor.mapPath_id path

theorem productSndMorphism_mapPath_eq
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    (left.productSndMorphism right).mapPath path = path := by
  change (Prefunctor.id Vertex).mapPath path = path
  exact Prefunctor.mapPath_id path

/-- Projecting product write-back to the first carrier recovers the complete
left write-back, not merely its trace coordinate. -/
theorem product_pathWriteBack_fst
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    residualTraceWriteBackMap
        (productFst (K := K) (E := E) (F := F))
        ((left.product right).pathWriteBack path) =
      left.pathWriteBack path := by
  have naturality :=
    (left.productFstMorphism right).pathWriteBack_naturality path
  rw [left.productFstMorphism_mapPath_eq right path] at naturality
  exact naturality

/-- Projecting product write-back to the second carrier recovers the complete
right write-back. -/
theorem product_pathWriteBack_snd
    (left : PathIndexedResidualTransport K E Vertex)
    (right : PathIndexedResidualTransport K F Vertex)
    {source target : Vertex}
    (path : Quiver.Path source target) :
    residualTraceWriteBackMap
        (productSnd (K := K) (E := E) (F := F))
        ((left.product right).pathWriteBack path) =
      right.pathWriteBack path := by
  have naturality :=
    (left.productSndMorphism right).pathWriteBack_naturality path
  rw [left.productSndMorphism_mapPath_eq right path] at naturality
  exact naturality

end PathIndexedResidualTransport
end ResidualProjection
end SaturationMonoid
