import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.SourceAbsolute
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeUnheatedTriadChannels NativeUnheatedTriadKernel
open NativeUnheatedStressPairEvolution
noncomputable section
variable {nu : Viscosity}

def jointRow (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) : ℂ :=
  ∑ slot : Fin 3, row seed slot wave i j output spectator indices time

theorem jointRow_original (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    jointRow seed wave i j output spectator indices time =
      ((decay nu (indices.2 + (wave-indices.1-indices.2)) indices.1)⁻¹ *
        (triadDecay nu indices.2 (wave-indices.1-indices.2) indices.1)⁻¹) •
      (pressure (indices.2 + (wave-indices.1-indices.2)) i j output *
        NativeUnheatedTriadTime.forcing seed (indices.2,i) (wave-indices.1-indices.2,j) (indices.1,spectator) time) := by
  have thirdValue (a b c : IntegerWavevector) : (![a,b,c] (2 : Fin 3)) = c := rfl
  simp only [jointRow, Fin.sum_univ_three, row, NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm,
    kernel, input, Fin.ext_iff, NativeUnheatedTriadTime.forcing,
    NativeUnheatedTriadRows.velocity_original, NativeUnheatedTriadRows.action,
    NativeUnheatedTriadRows.decode_apply, NativeUnheatedPairNegativeKernel.root,
    wholeVelocityCLM_apply, NativeUnheatedSourceWeightedTail.velocity]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num [Complex.real_smul, thirdValue]
  ring

theorem jointRow_next (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    jointRow seed wave i j output spectator indices (response.2.clockAdvance+time) =
      jointRow response.1 wave i j output spectator indices time := by
  simp only [jointRow_original, NativeUnheatedTriadTime.forcing_next seed _ _ _ response generated time nonnegative]

def joint (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) : ℂ :=
  ∑ slot : Fin 3, coefficient seed slot wave i j output spectator time

theorem joint_eq_tsum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    joint seed wave i j output spectator time =
      ∑' indices, jointRow seed wave i j output spectator indices time := by
  have same (slot : Fin 3) : coefficient seed slot wave i j output spectator time =
      ∑' indices, row seed slot wave i j output spectator indices time :=
    NativeUnheatedTriadSum.value_eq_tsum (kernel nu slot i j output) (cap nu)
      (kernel_bound nu slot i j output) wave i j spectator
      (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)
  simp only [joint, same, jointRow]
  exact (Summable.tsum_finsetSum (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 3))) =>
    (row_summable seed slot wave i j output spectator time).of_norm)).symm

theorem joint_bound (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    ‖joint seed wave i j output spectator time‖ ≤ 3 * bound seed * NativeUnheatedSourceGradient.mass seed time := by
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 3))) =>
    coefficient_bound seed slot wave i j output spectator time)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using paid

theorem joint_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (joint seed wave i j output spectator) (volume.restrict (Icc 0 horizon)) :=
  integrable_finsetSum _ (fun slot _ => coefficient_integrable seed slot wave i j output spectator horizon nonnegative)

theorem joint_next (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    joint seed wave i j output spectator (response.2.clockAdvance+time) =
      joint response.1 wave i j output spectator time := by
  simp only [joint_eq_tsum, jointRow_next seed wave i j output spectator _ response generated time nonnegative]

def quartic (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressCoefficient :=
  fun output spectator => -(∑ i : Coordinate, ∑ j : Coordinate,
    (joint seed wave i j spectator output time + joint seed wave i j output spectator time))

theorem quartic_row_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector)
    (output spectator : Coordinate) :
    ‖quartic seed time wave output spectator‖ ≤
      54 * bound seed * NativeUnheatedSourceGradient.mass seed time := by
  rw [quartic, norm_neg]
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Coordinate)) =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Coordinate)) =>
      (norm_add_le _ _).trans (add_le_add (joint_bound seed wave i j spectator output time)
        (joint_bound seed wave i j output spectator time)))))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at paid
  nlinarith only [paid]

theorem quartic_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    ‖quartic seed time wave‖ ≤ 54 * bound seed * NativeUnheatedSourceGradient.mass seed time := by
  have nonnegative : 0 ≤ 54 * bound seed * NativeUnheatedSourceGradient.mass seed time :=
    mul_nonneg (mul_nonneg (by norm_num) (bound_nonnegative seed)) (NativeUnheatedSourceGradient.mass_nonnegative seed time)
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  intro output
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  exact quartic_row_bound seed time wave output

theorem quartic_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (fun time => quartic seed time wave) (volume.restrict (Icc 0 horizon)) := by
  apply integrable_pi_iff.mpr
  intro output
  apply integrable_pi_iff.mpr
  intro spectator
  simpa only [quartic, Pi.neg_apply, Pi.add_apply] using!
    (integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
    (joint_integrable seed wave i j spectator output horizon nonnegative).add
      (joint_integrable seed wave i j output spectator horizon nonnegative)))).neg

theorem quartic_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    quartic seed (response.2.clockAdvance+time) = quartic response.1 time := by
  funext wave output spectator
  simp only [quartic, joint_next seed _ _ _ _ _ response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSource
