import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullSylvesterMatrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPropagationPencil SourcePropagationResolvent
open ActualDressedSylvester ActualDressedNoether ActualDressedFullCoulomb PreparationVacuumActionFieldLift
open scoped BigOperators Matrix
attribute [local irreducible] noetherStaticHalf noetherStaticInitial rawInitial dressedEulerObserver dressedStaticPolarization
  evolutionGenerator sourceInverse sourceInverseWeights driveOperator leftCurrent rightCurrent dressedKinematicPoint fieldUnit

/-- Both driven legs act on the original raw inverse before the complete source inverse is read. -/
theorem source_noether_half_matrix_return (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    noetherStaticHalf q reader force lambda =
      (∑ i : SourceIndex q, sourceInverseWeights q lambda i •
        (((evolutionGenerator q)^i.val) (noetherStaticInitial q reader force))) +
      ∑ i : SourceIndex q, ∑ j : SourceIndex q,
        (sourceInverseWeights q lambda i * sourceInverseWeights q lambda j) •
          (((evolutionGenerator q)^i.val) (driveOperator q force
            (((evolutionGenerator q)^j.val) (rawInitial q reader)))) := by
  have source : noetherStaticInitial q reader force -
      leftCurrent q force * sourceInverse q lambda (rawInitial q reader) +
        sourceInverse q lambda (rawInitial q reader) * rightCurrent q force =
      noetherStaticInitial q reader force + driveOperator q force (sourceInverse q lambda (rawInitial q reader)) := by
    rw [driveOperator_apply]
    abel
  have inner (i : SourceIndex q) :
      ((evolutionGenerator q)^i.val) (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) =
      ∑ j : SourceIndex q, sourceInverseWeights q lambda j •
        (((evolutionGenerator q)^i.val) (driveOperator q force (((evolutionGenerator q)^j.val) (rawInitial q reader)))) := by
    have actual := congrArg (fun B : ActualOperator =>
      ((evolutionGenerator q)^i.val) (driveOperator q force B))
      (source_inverse_matrix_return q lambda positive (rawInitial q reader))
    simpa only [map_sum, map_smul] using actual
  calc
    _ = sourceInverse q lambda (noetherStaticInitial q reader force -
        leftCurrent q force * sourceInverse q lambda (rawInitial q reader) +
          sourceInverse q lambda (rawInitial q reader) * rightCurrent q force) :=
      noether_static_half_inverse q reader force lambda positive
    _ = sourceInverse q lambda (noetherStaticInitial q reader force +
        driveOperator q force (sourceInverse q lambda (rawInitial q reader))) :=
      congrArg (sourceInverse q lambda) source
    _ = sourceInverse q lambda (noetherStaticInitial q reader force) +
        sourceInverse q lambda (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) := map_add _ _ _
    _ = (∑ i : SourceIndex q, sourceInverseWeights q lambda i •
        (((evolutionGenerator q)^i.val) (noetherStaticInitial q reader force))) +
        ∑ i : SourceIndex q, sourceInverseWeights q lambda i •
          (((evolutionGenerator q)^i.val) (driveOperator q force (sourceInverse q lambda (rawInitial q reader)))) :=
      congrArg₂ (fun (A B : ActualOperator) => A+B)
        (source_inverse_matrix_return q lambda positive (noetherStaticInitial q reader force))
        (source_inverse_matrix_return q lambda positive (driveOperator q force (sourceInverse q lambda (rawInitial q reader))))
    _ = _ := by
      apply congrArg (fun B : ActualOperator => _+B)
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (fun B : ActualOperator => sourceInverseWeights q lambda i • B) (inner i)).trans
        (by simp only [Finset.smul_sum, smul_smul])

/-- These are actual source words, not entries of a supplied realization or a replacement rest frame. -/
def sourceDirectMoments (event : DressedEvent) (transfer : PhysicalMomentum) (i j : Fin 289) :
    SourceIndex (dressedKinematicPoint event transfer) → ℂ := fun a =>
  dressedEulerObserver event (((evolutionGenerator (dressedKinematicPoint event transfer))^a.val)
    (noetherStaticInitial (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j)))

def sourceDrivenMoments (event : DressedEvent) (transfer : PhysicalMomentum) (i j : Fin 289) :
    Matrix (SourceIndex (dressedKinematicPoint event transfer))
      (SourceIndex (dressedKinematicPoint event transfer)) ℂ := fun a b =>
  dressedEulerObserver event (((evolutionGenerator (dressedKinematicPoint event transfer))^a.val)
    (driveOperator (dressedKinematicPoint event transfer) (fieldUnit j)
      (((evolutionGenerator (dressedKinematicPoint event transfer))^b.val)
        (rawInitial (dressedKinematicPoint event transfer) (fieldUnit i)))))

def sourceFullNoetherMatrixEntry (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (i j : Fin 289) : ℂ :=
  let weights := sourceInverseWeights (dressedKinematicPoint event transfer) lambda
  dotProduct weights (sourceDirectMoments event transfer i j) +
    dotProduct weights (sourceDrivenMoments event transfer i j *ᵥ weights)

/-- Full original Π is read by one generated finite matrix inverse and the original prepared observer. -/
theorem source_full_noether_polarization_matrix (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    dressedStaticPolarization event transfer lambda i j = sourceFullNoetherMatrixEntry event transfer lambda i j := by
  unfold dressedStaticPolarization
  rw [source_noether_half_matrix_return _ _ _ lambda positive]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  unfold sourceFullNoetherMatrixEntry sourceDirectMoments sourceDrivenMoments Matrix.mulVec dotProduct
  simp only [Finset.mul_sum, mul_assoc]
  apply congrArg (fun c : ℂ => _+c)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix
