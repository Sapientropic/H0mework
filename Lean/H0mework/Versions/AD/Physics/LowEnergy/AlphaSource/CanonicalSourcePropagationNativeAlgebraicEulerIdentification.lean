import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationSectorEulerIdentification
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeVariationDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineFormNativeGravityMultiplierAuxiliaryVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineFormNativeGaugeWedge
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineConjugateMatterVariation
open DiracExteriorMatterAction SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn StageNineLorentzConnectionVariation
open Stage9C.Material.SpinPair StageNineCoframeVariation StageNineTopologicalGravityCurvatureVariancePairing
open SourceQuantumScalarChart PreparationVacuumNativeSourceRestriction
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] nativeJetDensity nativeConfiguration nativePoint nativeEuler nativeLocalAction
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual

def algebraicSlot (field : Fin 289) : Prop :=
  (57 ≤ field.val ∧ field.val < 73) ∨ (97 ≤ field.val ∧ field.val < 121) ∨ 145 ≤ field.val

private theorem algebraic_not_retained (field : Fin 289) (algebraic : algebraicSlot field) (mu : Fin 4) :
    ¬retainedGradient mu field := by
  unfold algebraicSlot at algebraic
  unfold retainedGradient
  omega

private theorem algebraicGradient_effective_zero (field : Fin 289) (algebraic : algebraicSlot field) (mu : Fin 4) :
    effectiveJet (nativeJetBasis (some mu,field)) = 0 := by
  apply Prod.ext
  · rfl
  · funext nu entry
    change (if retainedGradient nu entry then (Pi.single mu (Pi.single field (1 : ℝ)) : Fin 4 → Field289) nu entry else 0) = 0
    by_cases same : entry=field
    · subst entry
      rw [if_neg (algebraic_not_retained field algebraic nu)]
    · by_cases sameMu : nu=mu
      · subst nu
        simp [same]
      · simp [sameMu]

private theorem algebraicGradient_ray (jet : NativeFirstJet) (field : Fin 289)
    (algebraic : algebraicSlot field) (mu : Fin 4) (r : ℝ) :
    nativeJetDensity (jet+r • nativeJetBasis (some mu,field)) = nativeJetDensity jet := by
  rw [←nativeJetDensity_effective (jet+r • nativeJetBasis (some mu,field)),
    map_add,map_smul,algebraicGradient_effective_zero field algebraic mu,smul_zero,add_zero,
    nativeJetDensity_effective]

/-- The ignored gradient is proved from the actual full-density projection, even off the differentiability domain. -/
theorem nativeAlgebraicMomentum_zero (point : BasePoint) (jet : NativeFirstJet)
    (field : Fin 289) (algebraic : algebraicSlot field) (mu : Fin 4) :
    fderiv ℝ (nativeLocalAction point) jet (nativeJetBasis (some mu,field)) = 0 := by
  rw [nativeLocalAction_atPoint]
  by_cases differentiable : DifferentiableAt ℝ nativeJetDensity jet
  · have ray : HasDerivAt (fun r : ℝ => jet+r • nativeJetBasis (some mu,field))
        (nativeJetBasis (some mu,field)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (nativeJetBasis (some mu,field))).const_add jet
    have generated := differentiable.hasFDerivAt.comp_hasDerivAt_of_eq 0 ray (by simp)
    have constant : (fun r : ℝ => nativeJetDensity (jet+r • nativeJetBasis (some mu,field))) =
        fun _ => nativeJetDensity jet := funext (algebraicGradient_ray jet field algebraic mu)
    change HasDerivAt (fun r : ℝ => nativeJetDensity (jet+r • nativeJetBasis (some mu,field))) _ 0 at generated
    rw [constant] at generated
    exact generated.unique (hasDerivAt_const 0 (nativeJetDensity jet))
  · rw [fderiv_zero_of_not_differentiableAt differentiable]
    rfl

/-- Every spacetime momentum derivative vanishes from its actual zero-valued source function. -/
theorem nativeAlgebraicMomentum_divergence_zero (signal : BasePoint → Field289) (point : BasePoint)
    (field : Fin 289) (algebraic : algebraicSlot field) (mu : Fin 4) :
    fieldDirectionalDerivative (fun position => fderiv ℝ (nativeLocalAction position)
      (signalFirstJet signal position) (nativeJetBasis (some mu,field))) point mu = 0 := by
  have constant : (fun position => fderiv ℝ (nativeLocalAction position)
      (signalFirstJet signal position) (nativeJetBasis (some mu,field))) = fun _ => (0 : ℝ) := by
    funext position
    exact nativeAlgebraicMomentum_zero position (signalFirstJet signal position) field algebraic mu
  rw [constant]
  simp [fieldDirectionalDerivative]

theorem nativeHolonomicEuler_algebraic_value (signal : BasePoint → Field289) (point : BasePoint)
    (field : Fin 289) (algebraic : algebraicSlot field) :
    nativeHolonomicEuler signal point field =
      fderiv ℝ (nativeLocalAction point) (signalFirstJet signal point) (nativeJetBasis (none,field)) := by
  unfold nativeHolonomicEuler
  simp only [nativeAlgebraicMomentum_divergence_zero signal point field algebraic,Finset.sum_const_zero,sub_zero]

private theorem unit_read_zero (field entry : Fin 289) (different : entry ≠ field) :
    (Pi.single field (1 : ℝ) : Field289) entry = 0 := by
  simp [different]

private theorem unit_shift_read (field entry : Fin 289) (different : entry ≠ field)
    (value : Field289) (r : ℝ) :
    (value+r • (Pi.single field (1 : ℝ) : Field289)) entry = value entry := by
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,unit_read_zero field entry different,mul_zero,add_zero]

private theorem algebraic_active_distinct (field entry : Fin 289) (algebraic : algebraicSlot field)
    (active : entry.val < 57 ∨ (73 ≤ entry.val ∧ entry.val < 97) ∨ (121 ≤ entry.val ∧ entry.val < 145)) :
    entry ≠ field := by
  intro equal
  have values := congrArg Fin.val equal
  unfold algebraicSlot at algebraic
  omega

private theorem algebraic_scalar_shift (field : Fin 289) (algebraic : algebraicSlot field)
    (value : Field289) (r : ℝ) :
    fieldScalar (value+r • Pi.single field 1) = fieldScalar value := by
  unfold fieldScalar
  apply Finset.sum_congr rfl
  intro j _
  have different : scalarSlot j ≠ field := algebraic_active_distinct field _ algebraic (by
    left
    simp only [scalarSlot,Fin.val_mk]
    omega)
  rw [unit_shift_read field (scalarSlot j) different]

private theorem algebraic_gauge_shift (field : Fin 289) (algebraic : algebraicSlot field)
    (value : Field289) (r : ℝ) (mu : Fin 4) :
    fieldGauge (value+r • Pi.single field 1) mu = fieldGauge value mu := by
  unfold fieldGauge
  apply Finset.sum_congr rfl
  intro j _
  have different : gaugeSlot mu j ≠ field := algebraic_active_distinct field _ algebraic (by
    left
    simp only [gaugeSlot,Fin.val_mk]
    omega)
  rw [unit_shift_read field (gaugeSlot mu j) different]

private theorem algebraic_lorentz_shift (field : Fin 289) (algebraic : algebraicSlot field)
    (value : Field289) (r : ℝ) :
    fieldLorentz (value+r • Pi.single field 1) = fieldLorentz value := by
  funext mu j
  apply unit_shift_read
  apply algebraic_active_distinct field _ algebraic
  right; right
  simp only [lorentzSlot,Fin.val_mk]
  omega

private theorem algebraic_primal_shift (field : Fin 289) (algebraic : algebraicSlot field)
    (value : Field289) (r : ℝ) :
    primalInsertion (value+r • Pi.single field 1) = primalInsertion value := by
  have each (part : Fin 2) (spin : Fin 4) (color : Fin 3) : primalSlot part spin color ≠ field :=
    algebraic_active_distinct field _ algebraic (by
      right; left
      simp only [primalSlot,Fin.val_mk]
      omega)
  simp only [primalInsertion,fieldPrimalComplex,fieldPrimal,unit_shift_read field _ (each _ _ _)]

private theorem gaugeB_shift (value force : Field289) (r : ℝ) :
    gaugeBInsertion (value+r • force) = gaugeBInsertion value+r • gaugeBInsertion force := by
  funext pair
  simp only [gaugeBInsertion,fieldGaugeB,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_smul,mul_smul,Finset.sum_add_distrib,←Finset.smul_sum,map_add,map_smul]

private theorem dual_shift (value force : Field289) (r : ℝ) :
    dualInsertion (value+r • force) = dualInsertion value+r • dualInsertion force := by
  apply LinearMap.ext
  intro v
  change (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex (value+r • force) spin color*sourceTripletRead (v spin) color) =
    (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex value spin color*sourceTripletRead (v spin) color)+
      (r : ℂ)*(∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex force spin color*sourceTripletRead (v spin) color)
  have coefficient (spin : Fin 4) (color : Fin 3) :
      fieldDualComplex (value+r • force) spin color = fieldDualComplex value spin color+(r : ℂ)*fieldDualComplex force spin color := by
    simp only [fieldDualComplex,fieldDual,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  simp only [coefficient,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro color _
  ring

private def algebraicPointRay (point : BasePoint) (field : StageNineContinuumPointField)
    (force : Field289) (r : ℝ) : StageNineContinuumPointField :=
  { field with
    coframe := field.coframe+r • fieldCoframe force
    gravityAuxiliary := field.gravityAuxiliary+r • fieldGravityB force
    gravitySimplicityMultiplier := field.gravitySimplicityMultiplier+r • fieldMultiplier force
    gaugeAuxiliary := field.gaugeAuxiliary+r • gaugeBInsertion force
    conjugateMatter := field.conjugateMatter+r • (dualInsertion force).comp (diracMatrixMatterAction (ActiveGauge.rotation point)) }

private theorem nativePoint_algebraic_shift (signal : BasePoint → Field289) (point : BasePoint)
    (field : Fin 289) (algebraic : algebraicSlot field) (r : ℝ) :
    nativePoint (fun x => signal x+r • Pi.single field 1) point =
      algebraicPointRay point (nativePoint signal point) (Pi.single field 1) r := by
  let original := nativeConfiguration signal
  let modified : StageNineHolonomicConfiguration :=
    { original with
      coframe := fun x => original.coframe x+r • fieldCoframe (Pi.single field 1)
      gravityAuxiliary := fun x => original.gravityAuxiliary x+r • fieldGravityB (Pi.single field 1)
      gravitySimplicityMultiplier := fun x => original.gravitySimplicityMultiplier x+r • fieldMultiplier (Pi.single field 1)
      gaugeAuxiliary := fun x => original.gaugeAuxiliary x+r • gaugeBInsertion (Pi.single field 1)
      conjugateMatter := fun x => original.conjugateMatter x+r •
        (dualInsertion (Pi.single field 1)).comp (diracMatrixMatterAction (ActiveGauge.rotation x)) }
  have configuration : nativeConfiguration (fun x => signal x+r • Pi.single field 1) = modified := by
    apply StageNineHolonomicConfiguration.ext
    · funext x a mu
      unfold modified original nativeConfiguration
      simp only [Matrix.add_apply,Matrix.smul_apply,fieldCoframe,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    · funext x
      unfold modified original nativeConfiguration
      dsimp only
      rw [algebraic_lorentz_shift field algebraic]
    · funext x a mu
      unfold modified original nativeConfiguration
      simp only [fieldGravityB,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    · funext x a mu
      unfold modified original nativeConfiguration
      simp only [fieldMultiplier,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    · funext x mu
      unfold modified original nativeConfiguration
      dsimp only
      rw [algebraic_gauge_shift field algebraic]
    · funext x
      unfold modified original nativeConfiguration
      dsimp only
      rw [gaugeB_shift]
      funext pair
      simp only [Pi.add_apply,Pi.smul_apply]
      abel
    · funext x
      unfold modified original nativeConfiguration
      dsimp only
      rw [algebraic_scalar_shift field algebraic]
    · funext x
      unfold modified original nativeConfiguration
      dsimp only
      rw [algebraic_primal_shift field algebraic]
    · funext x
      unfold modified original nativeConfiguration
      dsimp only
      rw [dual_shift]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.smul_apply]
      abel
  unfold nativePoint
  rw [configuration]
  apply StageNineContinuumPointField.ext <;> rfl

private theorem unit_coframe_zero (field : Fin 289) (outside : field.val < 57 ∨ 73 ≤ field.val) :
    fieldCoframe (Pi.single field 1) = 0 := by
  funext a mu
  apply unit_read_zero
  intro equal
  have values := congrArg Fin.val equal
  simp only [coframeSlot,Fin.val_mk] at values
  omega

private theorem unit_gravity_zero (field : Fin 289) (outside : field.val < 145 ∨ 181 ≤ field.val) :
    fieldGravityB (Pi.single field 1) = 0 := by
  funext a mu
  apply unit_read_zero
  intro equal
  have values := congrArg Fin.val equal
  simp only [gravitySlot,Fin.val_mk] at values
  omega

private theorem unit_multiplier_zero (field : Fin 289) (outside : field.val < 181 ∨ 217 ≤ field.val) :
    fieldMultiplier (Pi.single field 1) = 0 := by
  funext a mu
  apply unit_read_zero
  intro equal
  have values := congrArg Fin.val equal
  simp only [multiplierSlot,Fin.val_mk] at values
  omega

private theorem unit_gaugeB_zero (field : Fin 289) (outside : field.val < 217) :
    gaugeBInsertion (Pi.single field 1) = 0 := by
  funext pair
  have coefficient (a : Fin 12) : fieldGaugeB (Pi.single field 1) pair a = 0 := by
    apply unit_read_zero
    intro equal
    have values := congrArg Fin.val equal
    simp only [gaugeBSlot,Fin.val_mk] at values
    omega
  simp only [gaugeBInsertion,coefficient,zero_smul,Finset.sum_const_zero,map_zero,Pi.zero_apply]

private theorem unit_dual_zero (field : Fin 289) (outside : field.val < 97 ∨ 121 ≤ field.val) :
    dualInsertion (Pi.single field 1) = 0 := by
  have coefficient (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
      fieldDual (Pi.single field 1) part spin color = 0 := by
    apply unit_read_zero
    intro equal
    have values := congrArg Fin.val equal
    simp only [dualSlot,Fin.val_mk] at values
    omega
  apply LinearMap.ext
  intro v
  change (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex (Pi.single field 1) spin color*sourceTripletRead (v spin) color) = 0
  simp only [fieldDualComplex,coefficient,Complex.ofReal_zero,mul_zero,add_zero,zero_mul,Finset.sum_const_zero]

private theorem algebraicPointRay_multiplier (point : BasePoint) (state : StageNineContinuumPointField)
    (field : Fin 289) (range : 181 ≤ field.val ∧ field.val < 217) (r : ℝ) :
    algebraicPointRay point state (Pi.single field 1) r =
      withFormNativeGravityMultiplier state (state.gravitySimplicityMultiplier+r • fieldMultiplier (Pi.single field 1)) := by
  have coframe := unit_coframe_zero field (Or.inr (by omega))
  have gravity := unit_gravity_zero field (Or.inr range.1)
  have gauge := unit_gaugeB_zero field range.2
  have dual := unit_dual_zero field (Or.inr (by omega))
  apply StageNineContinuumPointField.ext <;>
    simp only [algebraicPointRay,withFormNativeGravityMultiplier,coframe,gravity,gauge,dual,
      smul_zero,add_zero,LinearMap.zero_comp]

private theorem algebraicPointRay_gravity (point : BasePoint) (state : StageNineContinuumPointField)
    (field : Fin 289) (range : 145 ≤ field.val ∧ field.val < 181) (r : ℝ) :
    algebraicPointRay point state (Pi.single field 1) r =
      withFormNativeGravityAuxiliary state (state.gravityAuxiliary+r • fieldGravityB (Pi.single field 1)) := by
  have coframe := unit_coframe_zero field (Or.inr (by omega))
  have multiplier := unit_multiplier_zero field (Or.inl range.2)
  have gauge := unit_gaugeB_zero field (by omega)
  have dual := unit_dual_zero field (Or.inr (by omega))
  apply StageNineContinuumPointField.ext <;>
    simp only [algebraicPointRay,withFormNativeGravityAuxiliary,coframe,multiplier,gauge,dual,
      smul_zero,add_zero,LinearMap.zero_comp]

private theorem algebraicPointRay_gauge (point : BasePoint) (state : StageNineContinuumPointField)
    (field : Fin 289) (range : 217 ≤ field.val) (r : ℝ) :
    algebraicPointRay point state (Pi.single field 1) r =
      withFormNativeP286GaugeAuxiliary state (state.gaugeAuxiliary+r • gaugeBInsertion (Pi.single field 1)) := by
  have coframe := unit_coframe_zero field (Or.inr (by omega))
  have gravity := unit_gravity_zero field (Or.inr (by omega))
  have multiplier := unit_multiplier_zero field (Or.inr range)
  have dual := unit_dual_zero field (Or.inr (by omega))
  apply StageNineContinuumPointField.ext <;>
    simp only [algebraicPointRay,withFormNativeP286GaugeAuxiliary,coframe,gravity,multiplier,dual,
      smul_zero,add_zero,LinearMap.zero_comp]

private theorem algebraicPointRay_coframe (point : BasePoint) (state : StageNineContinuumPointField)
    (field : Fin 289) (range : 57 ≤ field.val ∧ field.val < 73) (r : ℝ) :
    algebraicPointRay point state (Pi.single field 1) r =
      withCoframe state (state.coframe+r • fieldCoframe (Pi.single field 1)) := by
  have gravity := unit_gravity_zero field (Or.inl (by omega))
  have multiplier := unit_multiplier_zero field (Or.inl (by omega))
  have gauge := unit_gaugeB_zero field (by omega)
  have dual := unit_dual_zero field (Or.inl (by omega))
  apply StageNineContinuumPointField.ext <;>
    simp only [algebraicPointRay,withCoframe,gravity,multiplier,gauge,dual,
      smul_zero,add_zero,LinearMap.zero_comp]

private theorem algebraicPointRay_dual (point : BasePoint) (state : StageNineContinuumPointField)
    (field : Fin 289) (range : 97 ≤ field.val ∧ field.val < 121) (r : ℝ) :
    algebraicPointRay point state (Pi.single field 1) r =
      withConjugateMatter state (state.conjugateMatter+r •
        (dualInsertion (Pi.single field 1)).comp (diracMatrixMatterAction (ActiveGauge.rotation point))) := by
  have coframe := unit_coframe_zero field (Or.inr (by omega))
  have gravity := unit_gravity_zero field (Or.inl (by omega))
  have multiplier := unit_multiplier_zero field (Or.inl (by omega))
  have gauge := unit_gaugeB_zero field (by omega)
  apply StageNineContinuumPointField.ext <;>
    simp only [algebraicPointRay,withConjugateMatter,coframe,gravity,multiplier,gauge,
      smul_zero,add_zero]

private theorem nativeAlgebraicDensity_direction (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (field : Fin 289) (algebraic : algebraicSlot field) :
    HasDerivAt (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point)
      (nativeHolonomicEuler signal point field) 0 := by
  have generated := nativeDensity_variation_generated signal (fun _ => Pi.single field (1 : ℝ)) point
    smooth (differentiableAt_const _) inside
  have value : signalFirstJet (fun _ : BasePoint => Pi.single field (1 : ℝ)) point = nativeJetBasis (none,field) := by
    apply Prod.ext
    · rfl
    · funext mu
      simp [signalFirstJet,nativeJetBasis,fieldDirectionalDerivative]
  rw [value] at generated
  rw [nativeHolonomicEuler_algebraic_value signal point field algebraic,nativeLocalAction_atPoint]
  exact generated

theorem nativeMultiplierEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (field : Fin 289) (range : 181 ≤ field.val ∧ field.val < 217) :
    nativeHolonomicEuler signal point field =
      gravityTopologicalWedgeCoefficient (fieldMultiplier (Pi.single field 1)) (nativeEuler signal point).gravityMultiplier := by
  have algebraic : algebraicSlot field := Or.inr (Or.inr (by omega))
  have generated := nativeAlgebraicDensity_direction signal point smooth inside field algebraic
  have identity : (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point) =
      motherMultiplierCurve signal point (fieldMultiplier (Pi.single field 1)) := by
    funext r
    unfold nativeDensity motherMultiplierCurve
    change motherDensityAt point (nativePoint (fun x => signal x+r • Pi.single field 1) point) = _
    rw [nativePoint_algebraic_shift signal point field algebraic r,algebraicPointRay_multiplier point _ field range r]
  rw [identity] at generated
  exact generated.unique
    (motherMultiplierCurve_generated signal point (fieldMultiplier (Pi.single field 1)))

theorem nativeGravityAuxiliaryEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (field : Fin 289) (range : 145 ≤ field.val ∧ field.val < 181) :
    nativeHolonomicEuler signal point field =
      gravityTopologicalWedgeCoefficient (fieldGravityB (Pi.single field 1)) (nativeEuler signal point).gravityAuxiliary := by
  have algebraic : algebraicSlot field := Or.inr (Or.inr range.1)
  have generated := nativeAlgebraicDensity_direction signal point smooth inside field algebraic
  have identity : (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point) =
      motherGravityAuxiliaryCurve signal point (fieldGravityB (Pi.single field 1)) := by
    funext r
    unfold nativeDensity motherGravityAuxiliaryCurve
    change motherDensityAt point (nativePoint (fun x => signal x+r • Pi.single field 1) point) = _
    rw [nativePoint_algebraic_shift signal point field algebraic r,algebraicPointRay_gravity point _ field range r]
  rw [identity] at generated
  exact generated.unique (motherGravityAuxiliaryCurve_generated signal point (fieldGravityB (Pi.single field 1)))

theorem nativeGaugeAuxiliaryEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal point).coframe ≠ 0)
    (field : Fin 289) (range : 217 ≤ field.val) :
    nativeHolonomicEuler signal point field =
      formNativeP286GaugeWedgeCoefficient (gaugeBInsertion (Pi.single field 1)) (nativeEuler signal point).p286GaugeAuxiliary := by
  have algebraic : algebraicSlot field := Or.inr (Or.inr (by omega))
  have generated := nativeAlgebraicDensity_direction signal point smooth inside field algebraic
  have identity : (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point) =
      motherGaugeAuxiliaryCurve signal point (gaugeBInsertion (Pi.single field 1)) := by
    funext r
    unfold nativeDensity motherGaugeAuxiliaryCurve
    change motherDensityAt point (nativePoint (fun x => signal x+r • Pi.single field 1) point) = _
    rw [nativePoint_algebraic_shift signal point field algebraic r,algebraicPointRay_gauge point _ field range r]
  rw [identity] at generated
  exact generated.unique (motherGaugeAuxiliaryCurve_generated signal point (gaugeBInsertion (Pi.single field 1)) nondegenerate)

theorem nativeCoframeEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal point).coframe ≠ 0)
    (field : Fin 289) (range : 57 ≤ field.val ∧ field.val < 73) :
    nativeHolonomicEuler signal point field = (nativeEuler signal point).coframe (fieldCoframe (Pi.single field 1)) := by
  have algebraic : algebraicSlot field := Or.inl range
  have generated := nativeAlgebraicDensity_direction signal point smooth inside field algebraic
  have identity : (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point) =
      fun r => diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point (nativePoint signal point)
        ((nativePoint signal point).coframe+r • fieldCoframe (Pi.single field 1)) := by
    funext r
    unfold nativeDensity diracDualFormNativeCoframeLocalDensity
    rw [nativePoint_algebraic_shift signal point field algebraic r,algebraicPointRay_coframe point _ field range r]
  rw [identity] at generated
  exact generated.unique (motherCoframe_direction_generated signal point (Pi.single field 1) nondegenerate)

theorem nativeIndependentDualEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (field : Fin 289) (range : 97 ≤ field.val ∧ field.val < 121) :
    nativeHolonomicEuler signal point field = (nativeEuler signal point).conjugateMatter
      (matterDualCoordinates ((dualInsertion (Pi.single field 1)).comp (diracMatrixMatterAction (ActiveGauge.rotation point)))) := by
  have algebraic : algebraicSlot field := Or.inr (Or.inl range)
  have generated := nativeAlgebraicDensity_direction signal point smooth inside field algebraic
  have identity : (fun r : ℝ => nativeDensity (fun x => signal x+r • Pi.single field 1) point) =
      motherIndependentDualCurve signal point
        (matterDualCoordinates ((dualInsertion (Pi.single field 1)).comp (diracMatrixMatterAction (ActiveGauge.rotation point)))) := by
    funext r
    unfold nativeDensity motherIndependentDualCurve
    rw [matterDualOfCoordinates_surjective]
    change motherDensityAt point (nativePoint (fun x => signal x+r • Pi.single field 1) point) = _
    rw [nativePoint_algebraic_shift signal point field algebraic r,algebraicPointRay_dual point _ field range r]
  rw [identity] at generated
  exact generated.unique (motherIndependentDualCurve_generated signal point _)

end LowEnergy.SourcePropagationMotherResidualDirections
