import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.CanonicalContinuity
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.State

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame} {X : Type*} [TopologicalSpace X]

def normalizedOccupationCandidate (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) : Occupation source :=
  occupied * totalNormalization (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)

theorem normalized_occupation_candidate_eq (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    normalizedOccupationCandidate source positions occupied = normalizeOccupied source positions occupied enough := rfl

theorem occupied_fields_continuousAt (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (occupied : X → Occupation source) (currentPoint : X)
    (positionsContinuous : ContinuousAt positions currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint) (slot : ElectronIndex source.geometry) :
    ContinuousAt (fun point => occupiedFieldsAt source (positions point) (occupied point) slot) currentPoint := by
  classical
  exact tendsto_finsetSum Finset.univ fun index _ =>
    ((continuous_apply_apply index slot).continuousAt.comp occupiedContinuous).smul
      ((basis_hasFDerivAt source (positions currentPoint) index).continuousAt.comp positionsContinuous)

theorem normalized_occupation_candidate_continuousAt (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (occupied : X → Occupation source) (currentPoint : X)
    (positionsContinuous : ContinuousAt positions currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint)
    (good : Orthonormal ℂ (occupiedFieldsAt source (positions currentPoint) (occupied currentPoint))) :
    ContinuousAt (fun point => normalizedOccupationCandidate source (positions point) (occupied point)) currentPoint := by
  classical
  have normalizerContinuous := total_normalization_continuousAt
    (fun point => occupiedFieldsAt source (positions point) (occupied point)) currentPoint
    (occupied_fields_continuousAt source positions occupied currentPoint positionsContinuous occupiedContinuous)
    good.linearIndependent
  exact (continuous_fst.matrix_mul continuous_snd).continuousAt.comp
    (occupiedContinuous.prodMk normalizerContinuous)

theorem normalize_eventually_success (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (occupied : X → Occupation source) (currentPoint : X)
    (positionsContinuous : ContinuousAt positions currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint)
    (good : Orthonormal ℂ (occupiedFieldsAt source (positions currentPoint) (occupied currentPoint))) :
    ∀ᶠ point in 𝓝 currentPoint,
      normalize? source (positions point) (occupied point) =
        .ok (normalizedOccupationCandidate source (positions point) (occupied point)) := by
  have full := canonical_eventually_full_rank
    (fun point => occupiedFieldsAt source (positions point) (occupied point)) currentPoint
    (occupied_fields_continuousAt source positions occupied currentPoint positionsContinuous occupiedContinuous)
    good.linearIndependent
  filter_upwards [full] with point rankFull
  have enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ)
        (occupiedFieldsAt source (positions point) (occupied point)) := by
    rw [rankFull]
    simp only [ElectronIndex,Fintype.card_fin,le_refl]
  simp only [normalize?,dif_pos enough,normalized_occupation_candidate_eq source _ _ enough]

end
end CPS1PositivePulse
