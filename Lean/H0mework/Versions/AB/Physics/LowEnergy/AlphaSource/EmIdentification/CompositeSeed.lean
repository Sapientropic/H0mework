import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCutoff
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrentSeed

/-! The signed original Canonical seed supplies the grade condition. A section
keeps its caller's configuration profile; no new prepared state is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussYukawaGrade
open GaussUnitaryHistory (inclusion)
open FullYSourceCutoffVolterra
open scoped InnerProductSpace Topology

theorem original_seed_grade : fiberGrade CanonicalCompletedSector.seed=0 := by
  apply PiLp.ext
  intro word
  change (NativeHistoryGrade.sourceLabel word).2.val * CanonicalCompletedSector.seed word=0
  have h := congrArg (fun v : FockFiber => v word)
    CanonicalGradedCurrent.canonical_seed_N1_G0
  by_cases label : NativeHistoryGrade.sourceLabel word=(1,0)
  · simp [label]
  · have zero : CanonicalCompletedSector.seed word=0 := by
      simpa only [GaussCoreLabel.fiberPiece_apply,if_neg label] using h.symm
    rw [zero,mul_zero]

theorem original_seed_section_grade (f : QuantumTest) (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) : gradeCore f=0 := by
  apply DFunLike.ext
  intro z
  change fiberGrade (f z)=0
  rw [sameSource,map_smul,original_seed_grade,smul_zero]

theorem original_seed_composite_time (cut : ℕ) (s t : ℝ)
    (leftAddition rightAddition : Bool) (a u b v : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    inner ℂ (sourceSharpEvolution cut s (inclusion (leg leftAddition a u f)))
      (sourceEvolution cut t (inclusion (leg rightAddition b v g))) =
    inner ℂ (inclusion (leg leftAddition a u f))
      (GaussGradedUnitary.time (t-s) (inclusion (leg rightAddition b v g))) :=
  composite_two_time cut s t leftAddition rightAddition a u b v f g
    (original_seed_section_grade f profile sameSource)

theorem original_seed_composite_cutoff_limit (s t : ℝ)
    (leftAddition rightAddition : Bool) (a u b v : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    Filter.Tendsto (fun cut : ℕ =>
      inner ℂ (sourceSharpEvolution cut s (inclusion (leg leftAddition a u f)))
        (sourceEvolution cut t (inclusion (leg rightAddition b v g)))) Filter.atTop
      (𝓝 (inner ℂ (inclusion (leg leftAddition a u f))
        (GaussGradedUnitary.time (t-s) (inclusion (leg rightAddition b v g))))) := by
  simp only [original_seed_composite_time _ s t leftAddition rightAddition a u b v f g profile sameSource]
  exact tendsto_const_nhds

end LowEnergy.GaussComposite
