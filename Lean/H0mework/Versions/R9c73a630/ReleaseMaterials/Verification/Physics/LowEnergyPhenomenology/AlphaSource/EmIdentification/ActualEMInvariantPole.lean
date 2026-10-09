import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantCurvature

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMInvariantPole
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian PreparationVacuumMixedFieldReturn
open PreparationVacuumLowerClassical PreparationCoordinates
open ActualEMGaugeCurvature ActualEMDressedTransferIR ActualEMDressedGaugePole
open ActualDressedNoether ActualDressedFullCoulomb ActualEMCompleteOrbit ActualEMInvariantCurvature
open PreparationVacuumSoftPoleSelection PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet CanonicalGradedSpatialSource
open PreparationPhysicalNativePoleChargeReturn PreparationVacuumOriginalGreenFeedback
open PhysicalEMGaugeRealization Filter
open scoped BigOperators Matrix Topology
attribute [local irreducible] actual nativeGaugeLinearCurvature nativeBranchVector
  sourceGaugeCurvature0 fullGaugeCurvature invariantCurvatureRead dressedGaugePole dressedVoltageForcing

private theorem lie_derivation (a x y : P286LieBlockData) :
    p286LieBracket a (p286LieBracket x y)=
      p286LieBracket (p286LieBracket a x) y+p286LieBracket x (p286LieBracket a y) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket,suLieBracket]
    noncomm_ring
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket,suLieBracket]
      noncomm_ring
    · simp [p286LieBracket]

private theorem linear_constant (f : Field289) (pair : Fin 6) :
    nativeGaugeLinearCurvature (f,0) pair=
      rawCoordinates (p286CoordinateEquiv
        (p286LieBracket (actual.gaugeConnection 0 (pairFirst pair))
            (p286CoordinateEquiv.symm (fieldGauge f (pairSecond pair)))+
          p286LieBracket (p286CoordinateEquiv.symm (fieldGauge f (pairFirst pair)))
            (actual.gaugeConnection 0 (pairSecond pair)))) := by
  have zero (mu : Fin 4) : fieldGauge 0 mu=0 := by simp [fieldGauge]
  unfold nativeGaugeLinearCurvature nativeGaugeRawCurvature sourceGaugeCurvature0
    nativeGaugeQuadraticCurvature nativeGaugeCurvature
  simp only [Pi.zero_apply,zero,sub_self,map_zero,add_zero,map_add]
  abel

private theorem actual_curvature_bracket (pair : Fin 6) :
    holonomicGaugeCurvature actual 0 pair=
      p286LieBracket (actual.gaugeConnection 0 (pairFirst pair))
        (actual.gaugeConnection 0 (pairSecond pair)) := by
  have derivative (mu nu : Fin 4) : p286ConnectionDerivative actual 0 mu nu=0 := by
    simp [p286ConnectionDerivative,fieldDirectionalDerivative,actual_gaugeConnection]
  unfold holonomicGaugeCurvature
  rw [derivative,derivative,sub_self,zero_add]

/-- The original branch-zero gauge curvature is the generated background orbit; its scalar countervariation remains separate. -/
theorem native_origin_curvature_orbit (pair : Fin 6) :
    nativeGaugeLinearCurvature (sourceNativeOriginReal 0,0) pair=
      rawCoordinates (p286CoordinateEquiv
        (p286LieBracket emDirection (holonomicGaugeCurvature actual 0 pair))) := by
  rw [linear_constant,native_origin_gauge_orbit 0 (pairFirst pair),
    native_origin_gauge_orbit 0 (pairSecond pair)]
  change rawCoordinates (p286CoordinateEquiv
    (p286LieBracket (actual.gaugeConnection 0 (pairFirst pair))
        (p286LieBracket emDirection (actual.gaugeConnection 0 (pairSecond pair)))+
      p286LieBracket (p286LieBracket emDirection (actual.gaugeConnection 0 (pairFirst pair)))
        (actual.gaugeConnection 0 (pairSecond pair)))) = _
  rw [add_comm,←lie_derivation,actual_curvature_bracket]

private theorem branch_one_curvature_zero (pair : Fin 6) :
    nativeGaugeLinearCurvature (sourceNativeOriginReal 1,0) pair=0 := by
  rw [linear_constant,sourceNativeOriginReal_gauge,sourceNativeOriginReal_gauge]
  simp [p286LieBracket,suLieBracket]
  change p286CoordinateEquiv (0:P286LieBlockData)=0
  exact map_zero _

/-- Both generated source modes have zero first variation of every invariant curvature Gram entry at the origin. -/
theorem native_origin_invariant_first (branch : Fin 2) (pair other : Fin 6) :
    curvatureGramFirst (sourceNativeOriginReal branch,0) pair other=0 := by
  by_cases h : branch=0
  · subst branch
    unfold curvatureGramFirst
    rw [native_origin_curvature_orbit,native_origin_curvature_orbit]
    unfold sourceGaugeCurvature0
    rw [←rawGaugePair_source,←rawGaugePair_source]
    simp only [p286CoordinateLiePairing,LinearEquiv.symm_apply_apply]
    exact (add_comm _ _).trans (curvature_pair_orbit_balance emDirection
      (holonomicGaugeCurvature actual 0 pair) (holonomicGaugeCurvature actual 0 other))
  · have one : branch=1 := by omega
    subst branch
    simp only [curvatureGramFirst,branch_one_curvature_zero,rawGaugePair,Pi.zero_apply,
      zero_mul,mul_zero,add_zero]

private theorem fourier_origin_real (branch : Fin 2) :
    gaugeFourierJet 0 (nativeBranchVector branch) false=(sourceNativeOriginReal branch,0) := by
  apply Prod.ext
  · rfl
  · funext mu j
    simp [gaugeFourierJet]

private theorem fourier_origin_imag (branch : Fin 2) :
    gaugeFourierJet 0 (nativeBranchVector branch) true=(0:NativeFirstJet) := by
  apply Prod.ext
  · exact sourceNativeOriginImag_zero branch
  · funext mu j
    simp [gaugeFourierJet]

private theorem gram_zero_jet (pair other : Fin 6) : curvatureGramFirst 0 pair other=0 := by
  have zero (p : Fin 6) : nativeGaugeLinearCurvature 0 p=0 := by
    rw [gaugeLinearRaw_source]
    funext a
    simp [gaugeLinearRaw,gaugeFieldRaw,gaugeOriginalBracket]
  simp only [curvatureGramFirst,zero,rawGaugePair,Pi.zero_apply,zero_mul,mul_zero,add_zero]

theorem invariant_origin_mode (branch : Fin 2) (pair other : Fin 6) :
    invariantCurvatureRead 0 (nativeBranchVector branch) pair other=0 := by
  rw [invariant_curvature_original,fourier_origin_real,fourier_origin_imag,
    native_origin_invariant_first,gram_zero_jet]
  simp

/-- This map is generated by the source invariant observable; it can read the full coupled pencil without selecting a mode. -/
def invariantCurvatureMap (p : Fin 4→ℂ) (pair other : Fin 6) : (Fin 289→ℂ)→ₗ[ℂ]ℂ where
  toFun f:=invariantCurvatureRead p f pair other
  map_add' f g:=by
    unfold invariantCurvatureRead complexGaugePair fullGaugeCurvature
    simp only [map_add]
    ring
  map_smul' c f:=by
    unfold invariantCurvatureRead complexGaugePair fullGaugeCurvature
    simp only [map_smul,smul_eq_mul,RingHom.id_apply]
    ring

theorem invariant_origin_response (branch : Fin 2) (forcing : Fin 289→ℂ) (pair other : Fin 6) :
    invariantCurvatureRead 0 (leadingNativeResponse branch forcing) pair other=0 := by
  change invariantCurvatureMap 0 pair other
    (((softCoefficient branch:ℂ)*nativeBranchRead branch forcing) • nativeBranchVector branch)=0
  rw [map_smul]
  change _*invariantCurvatureRead 0 (nativeBranchVector branch) pair other=0
  rw [invariant_origin_mode,mul_zero]

/-- The actual moving creation-connected pole has no frequency-leading invariant-curvature Gram variation. -/
theorem dressed_invariant_frequency_leading (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) (pair other : Fin 6) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))*
      invariantCurvatureRead (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) pair other)
      scaleApproach (𝓝 0) := by
  have result := (invariant_curvature_continuous pair other).tendsto
    (0,leadingNativeResponse branch (dressedVoltageForcing event 0 0 T)) |>.comp
      ((sourceRay_soft_limit branch n unit).prodMk_nhds (dressed_soft_whole_pole event branch n unit T))
  rw [invariant_origin_response] at result
  apply result.congr'
  filter_upwards [] with e
  exact (invariantCurvatureMap _ pair other).map_smul _ _

end LowEnergy.GaussComposite.ActualEMInvariantPole
