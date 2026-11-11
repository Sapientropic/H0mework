import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Observed.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusForcedRegisteredRConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPairedWaveConsumer
open Complex BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Energy
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open scoped InnerProductSpace
open private outsideColumn_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource
namespace Root
export OriginalKPairedWaveRootSource (waveValue waveTrace wave_trace_source wave_value sourceScale source_scale_actual)
end Root
namespace S
export OriginalKPairedWaveActionSource
  (result rInput fourierInput projectionInput dilationInput input_binding
   dilation_equation projection_equation fourier_equation r_equation)
end S

local notation "h" => OriginalKBFiniteCalculation.fixedShift
local notation "u" => Root.sourceScale
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

private theorem shift_positive : 0 < h := by
  apply Real.log_pos
  change 1 < Real.sqrt 3
  exact Real.lt_sqrt_of_sq_lt (by norm_num)

private theorem shift_bounded : h ≤ Real.log 2 := by
  apply Real.log_le_log stageZeroSonineQ_pos
  change Real.sqrt 3 ≤ 2
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

theorem source_scale_ne_zero : u ≠ 0 := by
  rw [Root.source_scale_actual]
  exact div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.exp_pos _)))) two_ne_zero

private theorem paired_projection (shift : ℝ) (value : BurnolPaAmbientCarrier) :
    burnolEvenAmbientProjectionEndomorphism
        (pairedBurnolMultiplicativeDilation shift (value : BurnolL2)) =
      (burnolPairedAmbientCompression shift value : BurnolL2) := by
  change (burnolEvenAmbientProjection
    (pairedBurnolMultiplicativeDilation shift (value : BurnolL2)) : BurnolL2) = _
  apply congrArg Subtype.val
  unfold pairedBurnolMultiplicativeDilation burnolPairedAmbientCompression
    evenBurnolMultiplicativeCompression SourceGeneratedCompressedUnitaryDefectPort.compression
  simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, map_add, map_smul]
  rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

noncomputable def actualOutput : BurnolL2 :=
  (S.result observation nontrivial half depth ordinal).2.2.1

private theorem wave_value_native : Root.waveValue observation nontrivial half depth ordinal =
    ((u • Observed.sourceWave c h : BurnolPaAmbientCarrier) : BurnolL2) :=
  (Root.wave_value observation nontrivial half depth ordinal).trans
    (congrArg (fun point : BurnolL2 => u • point)
      (Observed.sourceWave_native c h shift_positive.le shift_bounded).1.symm)

/-- The subtype qualifies this occurrence's retained value; it supplies no replacement actor. -/
noncomputable def actualWave : BurnolPaAmbientCarrier :=
  ⟨Root.waveValue observation nontrivial half depth ordinal, by
    exact Eq.mp (congrArg (fun point : BurnolL2 =>
      point ∈ (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
      (wave_value_native observation nontrivial half depth ordinal).symm)
      (u • Observed.sourceWave c h : BurnolPaAmbientCarrier).property⟩

theorem actual_wave_source : actualWave observation nontrivial half depth ordinal =
    u • Observed.sourceWave c h :=
  Subtype.ext (wave_value_native observation nontrivial half depth ordinal)

theorem actual_wave_inPa : actualWave observation nontrivial half depth ordinal ∈
    burnolCompactCoPoissonClosedRange.toSubmodule :=
  Eq.mp (congrArg (fun point : BurnolPaAmbientCarrier =>
    point ∈ burnolCompactCoPoissonClosedRange.toSubmodule)
      (actual_wave_source observation nontrivial half depth ordinal).symm)
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem u
      (Observed.sourceWave_native c h shift_positive.le shift_bounded).2)

theorem actual_current_K_zero : inner ℂ (generatedK c)
    (Root.waveValue observation nontrivial half depth ordinal) = 0 := by
  have scaled : burnolCompletedMellinEvaluator c (u • Observed.sourceWave c h) = 0 :=
    (map_smul (burnolCompletedMellinEvaluator c) u (Observed.sourceWave c h)).trans
      ((congrArg (fun value : ℂ => u • value)
        (Observed.sourceWave_current_read c observation.mathlibZero h
          shift_positive.le shift_bounded)).trans (smul_zero u))
  have read := (congrArg (burnolCompletedMellinEvaluator c)
    (actual_wave_source observation nontrivial half depth ordinal)).trans scaled
  exact ((congrArg (fun kernel : BurnolL2 => inner ℂ kernel
    (Root.waveValue observation nontrivial half depth ordinal)) (generatedK_eq_original c)).trans
      (burnolCompletedMellinRieszVector_readback c
        (actualWave observation nontrivial half depth ordinal))).trans read

theorem actual_projection_source : (S.fourierInput observation nontrivial half depth ordinal).1 =
    (burnolPairedAmbientCompression h (actualWave observation nontrivial half depth ordinal) : BurnolL2) := by
  calc
    _ = burnolEvenAmbientProjectionEndomorphism
        (S.projectionInput observation nontrivial half depth ordinal).1 :=
      (S.projection_equation observation nontrivial half depth ordinal).symm
    _ = burnolEvenAmbientProjectionEndomorphism
        (pairedBurnolMultiplicativeDilation h
          (S.dilationInput observation nontrivial half depth ordinal).1) :=
      congrArg burnolEvenAmbientProjectionEndomorphism
        (S.dilation_equation observation nontrivial half depth ordinal).symm
    _ = burnolEvenAmbientProjectionEndomorphism
        (pairedBurnolMultiplicativeDilation h
          (Root.waveValue observation nontrivial half depth ordinal)) :=
      congrArg (fun point : BurnolL2 => burnolEvenAmbientProjectionEndomorphism
        (pairedBurnolMultiplicativeDilation h point))
        (S.input_binding observation nontrivial half depth ordinal)
    _ = _ := paired_projection h (actualWave observation nontrivial half depth ordinal)

noncomputable def actualPaired : BurnolPaAmbientCarrier :=
  ⟨(S.fourierInput observation nontrivial half depth ordinal).1, by
    exact Eq.mp (congrArg (fun point : BurnolL2 =>
      point ∈ (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
      (actual_projection_source observation nontrivial half depth ordinal).symm)
      (burnolPairedAmbientCompression h
        (actualWave observation nontrivial half depth ordinal)).property⟩

theorem actual_paired_source : actualPaired observation nontrivial half depth ordinal =
    burnolPairedAmbientCompression h (actualWave observation nontrivial half depth ordinal) :=
  Subtype.ext (actual_projection_source observation nontrivial half depth ordinal)

noncomputable def sourcePrice : ℂ :=
  (u / 2) * star (inner ℂ (positionSeed c h) (positionSeed c h) +
    inner ℂ (fourierSeed c h) (fourierSeed c h))

/-- The original K reads the actual physically projected child. -/
theorem actual_K_price : inner ℂ (generatedK c)
    (S.fourierInput observation nontrivial half depth ordinal).1 =
      sourcePrice observation nontrivial half := by
  have scaled : burnolCompletedMellinEvaluator c
      (burnolPairedAmbientCompression h (u • Observed.sourceWave c h)) =
        sourcePrice observation nontrivial half := by
    calc
      _ = u • burnolCompletedMellinEvaluator c
          (burnolPairedAmbientCompression h (Observed.sourceWave c h)) :=
        (congrArg (burnolCompletedMellinEvaluator c)
          (map_smul (burnolPairedAmbientCompression h) u (Observed.sourceWave c h))).trans
          (map_smul (burnolCompletedMellinEvaluator c) u
            (burnolPairedAmbientCompression h (Observed.sourceWave c h)))
      _ = u • ((1 / 2 : ℂ) * star
          (inner ℂ (positionSeed c h) (positionSeed c h) +
            inner ℂ (fourierSeed c h) (fourierSeed c h))) :=
        congrArg (fun value : ℂ => u • value)
          (Observed.sourceWave_next_read c observation.mathlibZero h
            shift_positive.le shift_bounded)
      _ = _ := by
        change u * ((1 / 2 : ℂ) * _) = (u / 2) * _
        ring
  have paired := (actual_paired_source observation nontrivial half depth ordinal).trans
    (congrArg (burnolPairedAmbientCompression h)
      (actual_wave_source observation nontrivial half depth ordinal))
  have read := (congrArg (burnolCompletedMellinEvaluator c) paired).trans scaled
  exact ((congrArg (fun kernel : BurnolL2 => inner ℂ kernel
    (S.fourierInput observation nontrivial half depth ordinal).1) (generatedK_eq_original c)).trans
      (burnolCompletedMellinRieszVector_readback c
        (actualPaired observation nontrivial half depth ordinal))).trans read

theorem source_price_ne_zero : sourcePrice observation nontrivial half ≠ 0 := by
  apply mul_ne_zero (div_ne_zero source_scale_ne_zero two_ne_zero)
  exact star_ne_zero.mpr
    (Margin.zero_owned_source_energy_ne_zero observation nontrivial half.down h shift_positive)

noncomputable def actualInput : BurnolPaAmbientCarrier :=
  ⟨(S.rInput observation nontrivial half depth ordinal).1, by
    exact Eq.mp (congrArg (fun point : BurnolL2 =>
      point ∈ (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
      (S.fourier_equation observation nontrivial half depth ordinal))
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
        (actualPaired observation nontrivial half depth ordinal)).property⟩

theorem actual_FK_price : inner ℂ (fourierL2 (generatedK c))
    (actualInput observation nontrivial half depth ordinal : BurnolL2) =
      sourcePrice observation nontrivial half :=
  (congrArg (fun point : BurnolL2 => inner ℂ (fourierL2 (generatedK c)) point)
    (S.fourier_equation observation nontrivial half depth ordinal).symm).trans
      ((fourierL2.inner_map_map (generatedK c)
        (S.fourierInput observation nontrivial half depth ordinal).1).trans
          (actual_K_price observation nontrivial half depth ordinal))

theorem actual_R_equation : burnolDirectRightResolventCLM c
    (actualInput observation nontrivial half depth ordinal : BurnolL2) =
      actualOutput observation nontrivial half depth ordinal :=
  S.r_equation observation nontrivial half depth ordinal

theorem actual_B_effect : outside (actualOutput observation nontrivial half depth ordinal) =
    (-2 * sourcePrice observation nontrivial half) • physicalOutsideColumn c := by
  have effect := original_R_physical_outside_source c
    (actualInput observation nontrivial half depth ordinal)
  exact (congrArg outside (actual_R_equation observation nontrivial half depth ordinal)).symm.trans
    (effect.trans (congrArg (fun value : ℂ => (-2 * value) • physicalOutsideColumn c)
      (actual_FK_price observation nontrivial half depth ordinal)))

theorem actual_complete_B_ne_zero : outside
    (actualOutput observation nontrivial half depth ordinal) ≠ 0 := by
  have nonzero := smul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0)
    (source_price_ne_zero observation nontrivial half))
    (outsideColumn_ne_zero observation nontrivial half)
  intro zero
  exact nonzero ((actual_B_effect observation nontrivial half depth ordinal).symm.trans zero)

theorem actual_complete_update : actualOutput observation nontrivial half depth ordinal =
    (burnolEvenAmbientProjection (actualOutput observation nontrivial half depth ordinal) : BurnolL2) +
      (-2 * sourcePrice observation nontrivial half) • physicalOutsideColumn c := by
  have whole := Submodule.starProjection_add_starProjection_orthogonal
    (K := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
    (actualOutput observation nontrivial half depth ordinal)
  change (burnolEvenAmbientProjection (actualOutput observation nontrivial half depth ordinal) : BurnolL2) +
    outside (actualOutput observation nontrivial half depth ordinal) = _ at whole
  exact whole.symm.trans (congrArg (fun residual : BurnolL2 =>
    (burnolEvenAmbientProjection (actualOutput observation nontrivial half depth ordinal) : BurnolL2) +
      residual) (actual_B_effect observation nontrivial half depth ordinal))

theorem actual_physical_energy :
    ‖(actualInput observation nontrivial half depth ordinal : BurnolL2)‖^2 -
      ‖(actualInput observation nontrivial half depth ordinal : BurnolL2) +
        (sourceDamping c : ℂ) •
          (burnolEvenAmbientProjection (actualOutput observation nontrivial half depth ordinal) : BurnolL2)‖^2 =
      4 * sourceDamping c^2 *
        ‖hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c)‖^2 *
          ‖sourcePrice observation nontrivial half‖^2 := by
  have energy := physical_forward_exact_loss c (actualInput observation nontrivial half depth ordinal)
  let cost : BurnolL2 → ℝ := fun output =>
    ‖(actualInput observation nontrivial half depth ordinal : BurnolL2)‖^2 -
      ‖(actualInput observation nontrivial half depth ordinal : BurnolL2) +
        (sourceDamping c : ℂ) • (burnolEvenAmbientProjection output : BurnolL2)‖^2
  exact ((congrArg cost (actual_R_equation observation nontrivial half depth ordinal)).symm.trans
    energy).trans (congrArg (fun value : ℂ => 4 * sourceDamping c^2 *
      ‖hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c)‖^2 * ‖value‖^2)
      (actual_FK_price observation nontrivial half depth ordinal))

theorem actual_physical_energy_pos : 0 <
    ‖(actualInput observation nontrivial half depth ordinal : BurnolL2)‖^2 -
      ‖(actualInput observation nontrivial half depth ordinal : BurnolL2) +
        (sourceDamping c : ℂ) •
          (burnolEvenAmbientProjection (actualOutput observation nontrivial half depth ordinal) : BurnolL2)‖^2 := by
  have damping := sourceDamping_pos c
  have power : 0 < ‖hPowerPhysicalCorrection
      (OriginalPrimitiveRankBalance.conjugateCoordinate c)‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
      (powerCorrection_ne_zero (OriginalPrimitiveRankBalance.conjugateCoordinate c)))
  have price : 0 < ‖sourcePrice observation nontrivial half‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (source_price_ne_zero observation nontrivial half))
  have positive : 0 < 4 * sourceDamping c^2 *
      ‖hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c)‖^2 *
        ‖sourcePrice observation nontrivial half‖^2 := by positivity
  exact Eq.mp (congrArg (fun amount : ℝ => 0 < amount)
    (actual_physical_energy observation nontrivial half depth ordinal).symm) positive

end OriginalWholeDebtRPairedWaveConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtRPairedWaveConsumer"
