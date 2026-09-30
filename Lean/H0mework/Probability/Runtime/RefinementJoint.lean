import H0mework.Probability.Runtime.RefinementCluster

/-! Two raw observations retain one complete joint-history fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedObservationRefinement

open SourceOperationNative SourceGeneratedActionObservationHistory
open SourceGeneratedScalarCofinalTopology SourceGeneratedScalarCofinalTopology.NativeProbability
open MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B D : Type u} [AddCommGroup B] [AddCommGroup D]
variable (leftRead : process.State → B) (rightRead : process.State → D)

def jointRead : process.State → B × D := fun state => (leftRead state, rightRead state)

abbrev fstFieldMap : Field (jointRead leftRead rightRead) →ₗ[ℤ] Field leftRead :=
  fieldMap (jointRead leftRead rightRead) (LinearMap.fst ℤ B D)

abbrev sndFieldMap : Field (jointRead leftRead rightRead) →ₗ[ℤ] Field rightRead :=
  fieldMap (jointRead leftRead rightRead) (LinearMap.snd ℤ B D)

theorem fstFieldMap_measurable :
    @Measurable _ _ (fieldBorel (jointRead leftRead rightRead)) (fieldBorel leftRead)
      (fstFieldMap leftRead rightRead) :=
  fieldMap_measurable (jointRead leftRead rightRead) (LinearMap.fst ℤ B D)

theorem sndFieldMap_measurable :
    @Measurable _ _ (fieldBorel (jointRead leftRead rightRead)) (fieldBorel rightRead)
      (sndFieldMap leftRead rightRead) :=
  fieldMap_measurable (jointRead leftRead rightRead) (LinearMap.snd ℤ B D)

abbrev fstCluster (runtime : LivingRuntimeState process) :
    HistoryCluster (jointRead leftRead rightRead) runtime → HistoryCluster leftRead runtime :=
  pushCluster (jointRead leftRead rightRead) (LinearMap.fst ℤ B D) runtime

abbrev sndCluster (runtime : LivingRuntimeState process) :
    HistoryCluster (jointRead leftRead rightRead) runtime → HistoryCluster rightRead runtime :=
  pushCluster (jointRead leftRead rightRead) (LinearMap.snd ℤ B D) runtime

/-- This inverse fibre requires both marginal witnesses to arise from the same joint cluster. -/
abbrev JointClusterFibre (runtime : LivingRuntimeState process)
    (left : HistoryCluster leftRead runtime) (right : HistoryCluster rightRead runtime) :=
  {joint : HistoryCluster (jointRead leftRead rightRead) runtime //
    fstCluster leftRead rightRead runtime joint = left ∧ sndCluster leftRead rightRead runtime joint = right}

theorem fstCluster_surjective [Finite B] [Finite D] (runtime : LivingRuntimeState process) :
    Function.Surjective (fstCluster leftRead rightRead runtime) :=
  pushCluster_surjective (jointRead leftRead rightRead) (LinearMap.fst ℤ B D) runtime

theorem sndCluster_surjective [Finite B] [Finite D] (runtime : LivingRuntimeState process) :
    Function.Surjective (sndCluster leftRead rightRead runtime) :=
  pushCluster_surjective (jointRead leftRead rightRead) (LinearMap.snd ℤ B D) runtime

variable (read : process.State → B)

theorem diagonal_fieldMaps : fstFieldMap read read = sndFieldMap read read := by
  let : UniformSpace (Field (jointRead read read)) := fieldUniform (jointRead read read)
  let : UniformSpace (Field read) := fieldUniform read
  let : T2Space (Field read) := field_t2 read
  have sourceDense := completionMap_denseRange
    (data (sourceAction process) (observer process (jointRead read read)))
    (compatible (sourceAction process) (observer process (jointRead read read)))
  have first : UniformContinuous (fstFieldMap read read) :=
    fieldMap_uniformContinuous (jointRead read read) (LinearMap.fst ℤ B B)
  have second : UniformContinuous (sndFieldMap read read) :=
    fieldMap_uniformContinuous (jointRead read read) (LinearMap.snd ℤ B B)
  have equality := sourceDense.equalizer first.continuous second.continuous (by
      funext word
      exact (fieldMap_source (jointRead read read) (LinearMap.fst ℤ B B) word).trans
        (fieldMap_source (jointRead read read) (LinearMap.snd ℤ B B) word).symm)
  exact DFunLike.coe_injective equality

theorem diagonal_measure_marginals
    (measure : @ProbabilityMeasure (Field (jointRead read read)) (fieldBorel (jointRead read read))) :
    letI : MeasurableSpace (Field (jointRead read read)) := fieldBorel (jointRead read read)
    letI : MeasurableSpace (Field read) := fieldBorel read
    measure.map (fstFieldMap_measurable read read).aemeasurable =
      measure.map (sndFieldMap_measurable read read).aemeasurable := by
  let : MeasurableSpace (Field (jointRead read read)) := fieldBorel (jointRead read read)
  let : MeasurableSpace (Field read) := fieldBorel read
  apply ProbabilityMeasure.toMeasure_injective
  change (measure : Measure (Field (jointRead read read))).map (fstFieldMap read read) =
    (measure : Measure (Field (jointRead read read))).map (sndFieldMap read read)
  rw [diagonal_fieldMaps]

theorem diagonal_cluster_marginals (runtime : LivingRuntimeState process)
    (cluster : HistoryCluster (jointRead read read) runtime) :
    fstCluster read read runtime cluster = sndCluster read read runtime cluster := by
  apply Subtype.ext
  exact diagonal_measure_marginals read cluster.val

theorem diagonal_fibre_nonempty_iff [Finite B] (runtime : LivingRuntimeState process)
    (left right : HistoryCluster read runtime) :
    Nonempty (JointClusterFibre read read runtime left right) ↔ left = right := by
  constructor
  · rintro ⟨⟨joint, leftEq, rightEq⟩⟩
    exact leftEq.symm.trans ((diagonal_cluster_marginals read runtime joint).trans rightEq)
  · rintro rfl
    obtain ⟨joint, leftEq⟩ := fstCluster_surjective read read runtime left
    exact ⟨⟨joint, leftEq, (diagonal_cluster_marginals read runtime joint).symm.trans leftEq⟩⟩

end
end SourceGeneratedObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
