import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualSignedSectorTime
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorJointFacts

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorSignedSectorRetarded
open SaturationMonoid.PhysicsCore
open ActualSignedSector ActiveMatterSectorCharge MixedSpectatorCandidate
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open FullYDynamicSource FullYDynamicResponse CompositeFullYBorn GeneralThreeParticleResponse
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder

def signedValue (dual : Bool) : ℝ := if dual then -3 else 3

theorem actual_candidate_fiber (dual : Bool) :
    fiberPiece (signedValue dual) (candidate dual) = candidate dual := by
  apply PiLp.ext
  intro word
  rw [fiberPiece_apply]
  by_cases h : value word = signedValue dual
  · simp only [if_pos h]
  · rw [if_neg h]
    symm
    have hw := congrFun (actual_candidate_active_sector dual) word
    change (∑ i ∈ word, (modeWeight i : ℂ)) * candidate dual word =
      (if dual then (-3 : ℂ) else 3) * candidate dual word at hw
    rw [←cast_value] at hw
    have hs : (signedValue dual : ℂ) = if dual then (-3 : ℂ) else 3 := by cases dual <;> norm_num [signedValue]
    rw [←hs] at hw
    have hd : (value word : ℂ)-(signedValue dual : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast h)
    have hz : ((value word : ℂ)-(signedValue dual : ℂ))*candidate dual word=0 := by linear_combination hw
    exact (mul_eq_zero.mp hz).resolve_left hd

theorem actual_candidate_core (dual : Bool) (f : ScalarTest) :
    project (signedValue dual) (candidateTest dual f) = candidateTest dual f := by
  apply DFunLike.ext
  intro z
  change fiberPiece (signedValue dual) (f z • candidate dual) = f z • candidate dual
  rw [map_smul,actual_candidate_fiber]

private theorem neutral_component (dual : Bool) (u : QuantumTest)
    (hu : project (signedValue dual) u = u) (word : Occupation) (neutral : value word=0)
    (z : SourceCoordinateSlice) : u z word=0 := by
  have hd : value word ≠ signedValue dual := by rw [neutral]; cases dual <;> norm_num [signedValue]
  have h := congrArg (fun v : QuantumTest => v z word) hu
  rw [project_apply,fiberPiece_apply] at h
  rw [if_neg hd] at h
  exact h.symm

/-- The same source candidate has zero neutral output at every frequency on
the original fullY and independent-sharp inverses over the generated cofinal range. -/
theorem actual_neutral_frequency (dual : Bool) (f : ScalarTest) (F : Index)
    (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ)
    (word : Occupation) (neutral : value word=0) (z : SourceCoordinateSlice) :
    literalResponse (saturate (signedValue dual) F) sharp (candidateTest dual f) advanced μ hμ w z word=0 :=
  neutral_component dual _
    (actual_response_sector _ F _ (actual_candidate_core dual f) sharp advanced μ hμ w) word neutral z

theorem actual_neutral_time (dual : Bool) (f : ScalarTest) (F : Index)
    (sharp : Bool) (t : ℝ) (word : Occupation) (neutral : value word=0) (z : SourceCoordinateSlice) :
    literalCoreTime (saturate (signedValue dual) F) sharp (candidateTest dual f) t z word=0 :=
  neutral_component dual _ (actual_time_sector _ F _ (actual_candidate_core dual f) sharp t) word neutral z

/-- The zero-past source wave is the original damped causal history, not a
new propagation map selected to obey the charge. -/
theorem actual_neutral_causal_wave (dual : Bool) (f : ScalarTest) (F : Index)
    (sharp advanced : Bool) (μ t : ℝ) (word : Occupation) (neutral : value word=0) :
    FullYPairedParseval.sourceWave (saturate (signedValue dual) F) sharp
      (candidateTest dual f) advanced μ t word=0 := by
  let q := candidateTest dual f
  let K := saturate (signedValue dual) F
  have sector : projection (signedValue dual) (FullYPairedParseval.sourceWave K sharp q advanced μ t) =
      FullYPairedParseval.sourceWave K sharp q advanced μ t := by
    unfold FullYPairedParseval.sourceWave FullYPairedParseval.causalWave
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht,map_smul,←embed_project,
        actual_time_sector _ F q (actual_candidate_core dual f)]
    · rw [Set.indicator_of_notMem ht,map_zero]
  have hd : value word ≠ signedValue dual := by rw [neutral]; cases dual <;> norm_num [signedValue]
  have h := congrArg (fun v : H => v word) sector
  rw [projection_apply,if_neg hd] at h
  exact h.symm

/-- The recently generated actual Y source is retained. No new source profile
or input invariance certificate is supplied by the caller. -/
theorem actual_generated_source_neutral_selection (dual : Bool) :
    ∃f : ScalarTest, f GaussHistoryHilbert.sourcePoint.val=1 ∧
      (∀F : Index, ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ, ∀w : ℝ,
        ∀word : Occupation, value word=0 → ∀z : SourceCoordinateSlice,
        literalResponse (saturate (signedValue dual) F) sharp (candidateTest dual f) advanced μ hμ w z word=0) ∧
      (∀F : Index, ∀sharp : Bool, ∀t : ℝ, ∀word : Occupation, value word=0 → ∀z : SourceCoordinateSlice,
        literalCoreTime (saturate (signedValue dual) F) sharp (candidateTest dual f) t z word=0) := by
  obtain ⟨f,hf,_⟩ := YukawaResolventDetection.actual_generated_candidate_Y_excess dual
  exact ⟨f,hf,actual_neutral_frequency dual f,actual_neutral_time dual f⟩

end LowEnergy.MixedSpectatorSignedSectorRetarded
