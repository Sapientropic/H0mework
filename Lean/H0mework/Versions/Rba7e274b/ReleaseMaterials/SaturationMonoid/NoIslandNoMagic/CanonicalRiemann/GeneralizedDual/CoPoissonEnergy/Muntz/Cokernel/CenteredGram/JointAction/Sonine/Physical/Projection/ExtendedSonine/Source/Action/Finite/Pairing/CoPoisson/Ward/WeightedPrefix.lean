import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prefix
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedProgram
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.ZeroRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

/-- The original weighted algorithm uses the same finitely centered primitive in every slot. -/
def weightedPrefix (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ) : BurnolL2 :=
  WeightedProgram.program lower upper f f' (Prefix.primitiveL2 N)

theorem weightedPrefix_eq_program (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ) :
    weightedPrefix lower upper f f' N =
      f upper • Prefix.prefixL2 lower upper N -
        ∫ u : ℝ in Ioc lower upper, f' u • Prefix.prefixL2 lower u N := rfl

/-- Finite counting and its continuous compensation converge together to the actual wave. -/
theorem weightedPrefix_tendsto (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (regular : ContinuousOn f' (Icc lower upper)) :
    Tendsto (weightedPrefix lower upper f f') atTop
      (𝓝 (burnolWeightedReciprocalStepWave lower upper f f')) := by
  simpa only [weightedPrefix, WeightedProgram.program_original] using!
    WeightedProgram.program_tendsto lower upper f f' positive regular
      Prefix.primitiveL2 burnolUnitCountingPrimitiveL2 Prefix.primitive_tendsto

def positionPrefix (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) (N : ℕ) : BurnolL2 :=
  weightedPrefix (bandLower shift) 4 (positionWeight coordinate shift)
    (deriv (positionWeight coordinate shift)) N

def fourierPrefix (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) (N : ℕ) : BurnolL2 :=
  weightedPrefix (bandLower shift) 4 (fourierWeight coordinate shift)
    (deriv (fourierWeight coordinate shift)) N

theorem positionPrefix_tendsto (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Tendsto (positionPrefix coordinate shift) atTop (𝓝 (positionWave coordinate shift)) :=
  weightedPrefix_tendsto _ _ _ _ (bandLower_pos shift)
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1))

theorem fourierPrefix_tendsto (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Tendsto (fourierPrefix coordinate shift) atTop (𝓝 (fourierWave coordinate shift)) :=
  weightedPrefix_tendsto _ _ _ _ (bandLower_pos shift)
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1))

/-- The original zero consumer reads the complete limit of the source-generated finite pairs. -/
theorem finite_signed_pair_tendsto_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    Tendsto (fun N =>
      inner ℂ (positionPrefix coordinate shift N) (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
      inner ℂ (fourierPrefix coordinate shift N)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) atTop (𝓝 0) := by
  have first : Continuous (fun value : BurnolL2 =>
      inner ℂ value (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by fun_prop
  have second : Continuous (fun value : BurnolL2 =>
      inner ℂ value (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) := by fun_prop
  have result := ((first.tendsto (positionWave coordinate shift)).comp
    (positionPrefix_tendsto coordinate shift)).sub
      ((second.tendsto (fourierWave coordinate shift)).comp (fourierPrefix_tendsto coordinate shift))
  simpa only [Function.comp_apply, positionWave_zero_read coordinate zero shift nonnegative bounded,
    fourierWave_zero_read coordinate zero shift nonnegative bounded, sub_zero] using result

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
