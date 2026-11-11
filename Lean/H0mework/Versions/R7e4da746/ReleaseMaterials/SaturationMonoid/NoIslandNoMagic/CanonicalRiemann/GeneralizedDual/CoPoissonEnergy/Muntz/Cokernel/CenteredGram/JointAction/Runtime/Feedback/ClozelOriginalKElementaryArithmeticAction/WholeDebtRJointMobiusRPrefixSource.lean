import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTateNormalization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRPrefixSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open OriginalKCrossParameterRAdjointSource
open scoped Topology InnerProductSpace BigOperators
namespace N
export OriginalWholeDebtRJointMobiusLocalNormalization (calculatedNormalization normalizationTest)
end N
namespace T
export OriginalWholeDebtRJointMobiusTateNormalization (tateSourceRaw tateKernel actual_tate_action)
end T
namespace D
export OriginalWholeDebtRJointMobiusRActionSource
  (sourceInput sourceNext actual_source_effect actual_complete_update)
end D
namespace C
export OriginalKCenteredMobiusRSource
  (sourceRRaw sourceRRaw_zero sourceRRaw_gap source_inverse_R_action)
end C
namespace M
export OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (actual_R_even_read)
end M
open private quarter_read_of_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open private divisionJet_ambientGapCoefficient_eq from H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator
local notation "q" => (1 / 4 : ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coordinate" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "nu" => N.calculatedNormalization coordinate
local notation "input" => D.sourceInput observation nontrivial half
local notation "next" => D.sourceNext observation nontrivial half

/-- This is the same generated L² input with its source-calculated exact q-face restored. -/
def inputRaw (x : ℝ) : ℂ :=
  if |x| ≤ q then nu else (input : BurnolL2) x

private theorem input_raw_zero : inputRaw observation nontrivial half 0 = nu := by
  simp [inputRaw]

private theorem input_raw_gap {x : ℝ} (inside : |x| ≤ q) :
    inputRaw observation nontrivial half x = inputRaw observation nontrivial half 0 := by
  rw [inputRaw, if_pos inside, input_raw_zero]

theorem actual_input_raw : (input : ℝ → ℂ) =ᵐ[volume] inputRaw observation nontrivial half := by
  have source := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (burnolAmbientGap_ae input)
  have normalized := OriginalWholeDebtRJointMobiusLocalNormalization.actual_normalization_read observation nontrivial half
  filter_upwards [source] with x atx
  unfold inputRaw
  by_cases inside : |x| ≤ q
  · rw [if_pos inside, normalized]
    exact atx (abs_le.mp inside)
  · rw [if_neg inside]

/-- The complete original inward action generates the next raw, including its zero-end counterterm. -/
def nextRaw : ℝ → ℂ := C.sourceRRaw coordinate (inputRaw observation nontrivial half)

def nextCoefficient : ℂ := -2 * nu / (coordinate).value

theorem actual_complete_prefix (x : ℝ) :
    nextRaw observation nontrivial half x = nextCoefficient observation nontrivial half -
      2 * ((|x| : ℝ) : ℂ) ^ (-(coordinate).value) *
        (∫ v : ℝ in (0 : ℝ)..|x|,
          (v : ℂ) ^ ((coordinate).value - 1) * (inputRaw observation nontrivial half v - nu)) := by
  unfold nextRaw OriginalKCenteredMobiusRSource.sourceRRaw OriginalKCenteredMobiusRSource.weightedCentered
  rw [input_raw_zero]
  rfl

/-- The existing original R reads the exact same input; the cofinal theorem is used only as a generic local operator law. -/
theorem actual_next_raw : (next : ℝ → ℂ) =ᵐ[volume] nextRaw observation nontrivial half := by
  have even : reflectL2 (input : BurnolL2) = input := mem_evenL2ClosedFace_iff.mp (input).property.2
  change (burnolDirectRightResolvent ((coordinate).value / 2) (input : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  exact M.actual_R_even_read coordinate input (inputRaw observation nontrivial half)
    (actual_input_raw observation nontrivial half) (input_raw_gap observation nontrivial half) even

theorem actual_next_native : MemLp (nextRaw observation nontrivial half) 2 volume :=
  (Lp.memLp next).ae_eq (actual_next_raw observation nontrivial half)

theorem actual_next_zero : nextRaw observation nontrivial half 0 = nextCoefficient observation nontrivial half := by
  rw [nextRaw, C.sourceRRaw_zero, input_raw_zero]
  rfl

theorem actual_next_gap {x : ℝ} (inside : |x| ≤ q) :
    nextRaw observation nontrivial half x = nextCoefficient observation nontrivial half := by
  rw [nextRaw, C.sourceRRaw_gap coordinate _ (input_raw_gap observation nontrivial half) inside, input_raw_zero]
  rfl

/-- The true Tate integral, rather than a receiver-selected mean, generates the infinite R counterterm. -/
theorem actual_zero_end_from_Tate_source :
    nextCoefficient observation nontrivial half =
      -2 / (coordinate).value *
        (∫ t : ℝ in Ioi 0, T.tateSourceRaw coordinate t * T.tateKernel N.normalizationTest t) := by
  rw [(T.actual_tate_action coordinate N.normalizationTest).2]
  unfold nextCoefficient OriginalWholeDebtRJointMobiusLocalNormalization.calculatedNormalization
  ring

/-- The complete R next's position face is generated before any physical projection. -/
theorem actual_next_restriction :
    burnolQuarterRestriction next = nextCoefficient observation nontrivial half • intervalConstant q := by
  have source := quarter_read_of_source next (nextRaw observation nontrivial half)
    (actual_next_raw observation nontrivial half)
    (fun inside => (actual_next_gap observation nontrivial half inside).trans (actual_next_zero observation nontrivial half).symm)
  rw [actual_next_zero] at source
  exact source

theorem actual_next_positionGap : next ∈ locallyConstantFace q := by
  rw [mem_locallyConstantFace_iff_exists]
  exact ⟨nextCoefficient observation nontrivial half, (actual_next_restriction observation nontrivial half).symm⟩

theorem actual_next_mean : burnolAmbientGapCoefficient q next = nextCoefficient observation nontrivial half :=
  divisionJet_ambientGapCoefficient_eq q (by norm_num) next _ (actual_next_restriction observation nontrivial half).symm

/-- Full Möbius inversion consumes the complete same next and its native prefix, without fixed-window admission. -/
theorem actual_next_inverse_source (t : ℝ) (positive : 0 < t) :
    burnolCenteredMobiusInverse (nextRaw observation nontrivial half) t =
      -2 * (t : ℂ) ^ (-(coordinate).value) *
        (∫ v : ℝ in (0 : ℝ)..t, (v : ℂ) ^ ((coordinate).value - 1) *
          burnolCenteredMobiusInverse (inputRaw observation nontrivial half) v) := by
  exact C.source_inverse_R_action coordinate (inputRaw observation nontrivial half)
    ((Lp.memLp (input : BurnolL2)).ae_eq (actual_input_raw observation nontrivial half))
    (input_raw_gap observation nontrivial half) t positive

/-- The physical projection retains the entire original B column cost alongside the generated zero-end face. -/
theorem actual_physical_next_position_update :
    burnolQuarterRestriction (burnolEvenAmbientProjection next : BurnolL2) =
      nextCoefficient observation nontrivial half • intervalConstant q -
        (2 * OriginalNextEndpointProgramme.programmePrice coordinate (Real.log stageZeroSonineQ)) •
          burnolQuarterRestriction (PhysicalOutsideSource.physicalOutsideColumn coordinate) := by
  have whole := congrArg burnolQuarterRestriction (D.actual_complete_update observation nontrivial half)
  rw [map_add, map_smul, actual_next_restriction] at whole
  exact eq_sub_iff_add_eq.mpr whole.symm

end OriginalWholeDebtRJointMobiusRPrefixSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
