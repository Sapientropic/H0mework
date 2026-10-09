import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeVariationDirections
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationSectorEulerIdentification
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeScalarEulerIdentification

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineMatterVariation
open StageNineMatterPointwiseEquation StageNineMatterCovariantDerivativeAffine
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineLorentzConnectionVariation DiracExteriorMatterAction
open StageNineDiracMatterCoordinateCalculus PointwiseDiracSpinConnectionLift StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariation
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction
open Stage9C.Material.SpinPair ActiveGauge
open Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] nativeConfiguration nativePoint nativeEuler nativeJetDensity
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual

private theorem primalSlot_eq_iff (part part' : Fin 2) (spin spin' : Fin 4) (color color' : Fin 3) :
    primalSlot part spin color = primalSlot part' spin' color' ↔ part=part' ∧ spin=spin' ∧ color=color' := by
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [primalSlot,Fin.val_mk] at values
    have p : part.val=part'.val := by omega
    have s : spin.val=spin'.val := by omega
    have c : color.val=color'.val := by omega
    exact ⟨Fin.ext p,Fin.ext s,Fin.ext c⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

private def primalCoefficientForce (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) : Field289 :=
  coefficient.re • Pi.single (primalSlot 0 spin color) 1+
    coefficient.im • Pi.single (primalSlot 1 spin color) 1

private theorem primalCoefficientForce_read (spin spin' : Fin 4) (color color' : Fin 3) (coefficient : ℂ) :
    fieldPrimalComplex (primalCoefficientForce spin color coefficient) spin' color' =
      if spin'=spin ∧ color'=color then coefficient else 0 := by
  have representation : (coefficient.re : ℂ)+Complex.I*(coefficient.im : ℂ)=coefficient := by
    apply Complex.ext <;> simp
  simp only [primalCoefficientForce,fieldPrimalComplex,fieldPrimal,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply,primalSlot_eq_iff]
  by_cases same : spin'=spin ∧ color'=color
  · rcases same with ⟨rfl,rfl⟩
    simpa using representation
  · simp [same]

private theorem primalCoefficientForce_insertion (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    primalInsertion (primalCoefficientForce spin color coefficient) = coefficient • sourceTripletLeg spin color := by
  unfold primalInsertion
  simp only [primalCoefficientForce_read,ite_smul,zero_smul]
  simp [ite_and]

private theorem primalCoefficientForce_outside (spin : Fin 4) (color : Fin 3) (coefficient : ℂ)
    (entry : Fin 289) (outside : entry.val < 73 ∨ 97 ≤ entry.val) :
    primalCoefficientForce spin color coefficient entry = 0 := by
  have different (part : Fin 2) : entry ≠ primalSlot part spin color := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [primalSlot,Fin.val_mk] at values
    omega
  simp [primalCoefficientForce,different]

private def primalPartCoefficient (part : Fin 2) : ℂ := if part=0 then 1 else Complex.I

private theorem primalCoefficientForce_unit (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    primalCoefficientForce spin color (primalPartCoefficient part) = Pi.single (primalSlot part spin color) 1 := by
  fin_cases part <;> simp [primalCoefficientForce,primalPartCoefficient]

private def inversePhaseComponent (point : BasePoint) (spin : Fin 4) : ℂ :=
  (inverseRotation point) spin spin

private theorem phase_inverse_component (point : BasePoint) (spin : Fin 4) :
    phaseComponents point spin*inversePhaseComponent point spin = 1 := by
  fin_cases spin <;>
    simp only [phaseComponents,inversePhaseComponent,inverseRotation,Matrix.diagonal_apply]
  all_goals first
    | exact upper_lower_product point
    | rw [mul_comm]; exact upper_lower_product point

private theorem inversePhaseComponent_smooth (spin : Fin 4) :
    ContDiff ℝ ∞ (fun point => inversePhaseComponent point spin) := by
  fin_cases spin <;> first
    | simpa [inversePhaseComponent,inverseRotation,lowerPhase] using phase_smooth (-frequency)
    | simpa [inversePhaseComponent,inverseRotation,upperPhase] using phase_smooth frequency

private def primalUnrotation (point : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ)
    (position : BasePoint) : Field289 :=
  primalCoefficientForce spin color (inversePhaseComponent position spin*phaseComponents point spin*coefficient)

private theorem primalUnrotation_smooth (point : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    ContDiff ℝ ∞ (primalUnrotation point spin color coefficient) := by
  have smooth : ContDiff ℝ ∞ (fun position : BasePoint => inversePhaseComponent position spin*phaseComponents point spin*coefficient) :=
    ((inversePhaseComponent_smooth spin).mul contDiff_const).mul contDiff_const
  unfold primalUnrotation primalCoefficientForce
  exact ((Complex.reCLM.contDiff.comp smooth).smul contDiff_const).add
    ((Complex.imCLM.contDiff.comp smooth).smul contDiff_const)

private theorem primalUnrotation_value (point : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    primalUnrotation point spin color coefficient point = primalCoefficientForce spin color coefficient := by
  unfold primalUnrotation
  rw [mul_comm (inversePhaseComponent point spin) (phaseComponents point spin),phase_inverse_component,one_mul]

private theorem rotation_tripletLeg (point : BasePoint) (spin : Fin 4) (color : Fin 3) :
    diracMatrixMatterAction (ActiveGauge.rotation point) (sourceTripletLeg spin color) =
      phaseComponents point spin • sourceTripletLeg spin color := by
  funext row
  simp [diracMatrixMatterAction,ActiveGauge.rotation,phaseComponents,sourceTripletLeg,
    Pi.single_apply,Matrix.diagonal_apply]
  by_cases same : row=spin
  · subst row
    rfl
  · simp [same]

private theorem primalUnrotation_physical (point position : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    diracMatrixMatterAction (ActiveGauge.rotation position)
      (primalInsertion (primalUnrotation point spin color coefficient position)) =
      diracMatrixMatterAction (ActiveGauge.rotation point)
        (primalInsertion (primalCoefficientForce spin color coefficient)) := by
  unfold primalUnrotation
  rw [primalCoefficientForce_insertion,primalCoefficientForce_insertion,map_smul,map_smul,
    rotation_tripletLeg,rotation_tripletLeg,smul_smul,smul_smul]
  congr 1
  calc
    (inversePhaseComponent position spin*phaseComponents point spin*coefficient)*phaseComponents position spin =
        (phaseComponents position spin*inversePhaseComponent position spin)*phaseComponents point spin*coefficient := by ring
    _ = coefficient*phaseComponents point spin := by rw [phase_inverse_component]; ring

private def primalSupported (force : Field289) : Prop :=
  ∀ entry : Fin 289,entry.val < 73 ∨ 97 ≤ entry.val → force entry=0

private theorem primalForce_supported (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    primalSupported (primalCoefficientForce spin color coefficient) :=
  primalCoefficientForce_outside spin color coefficient

private theorem primalUnrotation_supported (point position : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    primalSupported (primalUnrotation point spin color coefficient position) :=
  primalForce_supported _ _ _

private theorem primal_scalar_zero (force : Field289) (supported : primalSupported force) : fieldScalar force=0 := by
  unfold fieldScalar
  have each (j : Fin 9) : force (scalarSlot j)=0 := supported _ (Or.inl (by simp only [scalarSlot];omega))
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem primal_gauge_zero (force : Field289) (supported : primalSupported force) (mu : Fin 4) : fieldGauge force mu=0 := by
  unfold fieldGauge
  have each (j : Fin 12) : force (gaugeSlot mu j)=0 := supported _ (Or.inl (by simp only [gaugeSlot];omega))
  simp only [each,zero_smul,Finset.sum_const_zero]

private theorem primal_lorentz_zero (force : Field289) (supported : primalSupported force) : fieldLorentz force=0 := by
  funext mu a
  exact supported _ (Or.inr (by simp only [lorentzSlot];omega))

private theorem primal_dual_zero (force : Field289) (supported : primalSupported force) (spin : Fin 4) (color : Fin 3) :
    fieldDualComplex force spin color=0 := by
  have each (part : Fin 2) : fieldDual force part spin color=0 := supported _ (Or.inr (by simp only [dualSlot];omega))
  simp only [fieldDualComplex,each,Complex.ofReal_zero,mul_zero,add_zero]

private theorem primalInsertion_real_smul (r : ℝ) (value : DiracExteriorMatterCarrier) :
    matterCoordinateEquiv (r • value)=r • matterCoordinateEquiv value := by
  change matterCoordinateEquiv ((r : ℂ) • value)=(r : ℂ) • matterCoordinateEquiv value
  exact map_smul matterCoordinateEquiv (r : ℂ) value

private theorem primalInsertion_shift (value force : Field289) (r : ℝ) :
    primalInsertion (value+r • force)=primalInsertion value+r • primalInsertion force := by
  apply matterCoordinateEquiv.injective
  rw [map_add,primalInsertion_real_smul]
  change primalInsertionCLM (value+r • force)=primalInsertionCLM value+r • primalInsertionCLM force
  rw [map_add,map_smul]

private theorem matrixMatter_real_smul (matrix : DiracCliffordRepresentation.DiracMatrix) (r : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction matrix (r • matter)=r • diracMatrixMatterAction matrix matter := by
  change diracMatrixMatterAction matrix ((r : ℂ) • matter)=(r : ℂ) • diracMatrixMatterAction matrix matter
  exact map_smul (diracMatrixMatterAction matrix) (r : ℂ) matter

private theorem complexLinear_real_smul (action : DiracExteriorMatterCarrier →ₗ[ℂ] DiracExteriorMatterCarrier)
    (r : ℝ) (matter : DiracExteriorMatterCarrier) : action (r • matter)=r • action matter := by
  change action ((r : ℂ) • matter)=(r : ℂ) • action matter
  exact map_smul action (r : ℂ) matter

private theorem matterRealZero (matter : DiracExteriorMatterCarrier) : (0 : ℝ) • matter=0 := by
  change (0 : ℂ) • matter=0
  exact zero_smul ℂ matter

private theorem nativePrimal_configurationShift (signal variation : BasePoint → Field289)
    (supported : ∀ x,primalSupported (variation x)) (r : ℝ) :
    nativeConfiguration (fun x => signal x+r • variation x) =
      { (nativeConfiguration signal) with matter := (fun x => (nativeConfiguration signal).matter x+
          r • (diracMatrixMatterAction (ActiveGauge.rotation x) (primalInsertion (variation x)))) } := by
  apply StageNineHolonomicConfiguration.ext
  · funext x a mu
    unfold nativeConfiguration
    change actual.coframe x a mu+(signal x+r • variation x) (coframeSlot a mu)=
      actual.coframe x a mu+signal x (coframeSlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (Or.inl (by simp only [coframeSlot];omega)),mul_zero,add_zero]
  · funext x
    unfold nativeConfiguration
    dsimp only
    have same : fieldLorentz (signal x+r • variation x)=fieldLorentz (signal x) := by
      funext mu a
      change (signal x+r • variation x) (lorentzSlot mu a)=signal x (lorentzSlot mu a)
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [supported x _ (Or.inr (by simp only [lorentzSlot];omega)),mul_zero,add_zero]
    rw [same]
  · funext x a mu
    unfold nativeConfiguration
    change actual.gravityAuxiliary x a mu+(signal x+r • variation x) (gravitySlot a mu)=
      actual.gravityAuxiliary x a mu+signal x (gravitySlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (Or.inr (by simp only [gravitySlot];omega)),mul_zero,add_zero]
  · funext x a mu
    unfold nativeConfiguration
    change actual.gravitySimplicityMultiplier x a mu+(signal x+r • variation x) (multiplierSlot a mu)=
      actual.gravitySimplicityMultiplier x a mu+signal x (multiplierSlot a mu)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [supported x _ (Or.inr (by simp only [multiplierSlot];omega)),mul_zero,add_zero]
  · funext x mu
    unfold nativeConfiguration
    dsimp only
    rw [fieldGauge_add,fieldGauge_smul,primal_gauge_zero _ (supported x),smul_zero,add_zero]
  · funext x pair
    unfold nativeConfiguration
    dsimp only
    have same : gaugeBInsertion (signal x+r • variation x) pair=gaugeBInsertion (signal x) pair := by
      unfold gaugeBInsertion fieldGaugeB
      apply congrArg p286CoordinateEquiv.symm
      apply Finset.sum_congr rfl
      intro a _
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [supported x _ (Or.inr (by simp only [gaugeBSlot];omega)),mul_zero,add_zero]
    rw [same]
  · funext x
    unfold nativeConfiguration
    dsimp only
    rw [fieldScalar_add,fieldScalar_smul,primal_scalar_zero _ (supported x),smul_zero,add_zero]
  · funext x
    unfold nativeConfiguration
    dsimp only
    rw [primalInsertion_shift,map_add,matrixMatter_real_smul]
    abel
  · funext x
    unfold nativeConfiguration
    dsimp only
    have same : dualInsertion (signal x+r • variation x)=dualInsertion (signal x) := by
      apply LinearMap.ext
      intro v
      have each (spin : Fin 4) (color : Fin 3) :
          fieldDualComplex (signal x+r • variation x) spin color=fieldDualComplex (signal x) spin color := by
        have linear : dualCoefficientCLM spin color (variation x)=0 := primal_dual_zero _ (supported x) spin color
        change dualCoefficientCLM spin color (signal x+r • variation x)=dualCoefficientCLM spin color (signal x)
        rw [map_add,map_smul,linear,smul_zero,add_zero]
      simp only [dualInsertion,each]
    rw [same]

private theorem nativePrimal_fixed_configuration (signal : BasePoint → Field289) (point : BasePoint)
    (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) (weight : BasePoint → ℝ) (r : ℝ) :
    nativeConfiguration (fun x => signal x+r • (weight x • primalUnrotation point spin color coefficient x)) =
      { nativeConfiguration signal with matter := fun x => (nativeConfiguration signal).matter x+
        r • (weight x • diracMatrixMatterAction (ActiveGauge.rotation point)
          (primalInsertion (primalCoefficientForce spin color coefficient))) } := by
  have supported : ∀ x,primalSupported (weight x • primalUnrotation point spin color coefficient x) := by
    intro x entry outside
    simp only [Pi.smul_apply,smul_eq_mul,primalUnrotation_supported point x spin color coefficient entry outside,mul_zero]
  rw [nativePrimal_configurationShift signal _ supported r]
  apply StageNineHolonomicConfiguration.ext
  all_goals try rfl
  funext x
  have insertion : primalInsertion (weight x • primalUnrotation point spin color coefficient x)=
      weight x • primalInsertion (primalUnrotation point spin color coefficient x) := by
    have generated := primalInsertion_shift 0 (primalUnrotation point spin color coefficient x) (weight x)
    simpa only [zero_add,primalInsertion_zero] using generated
  change (nativeConfiguration signal).matter x+r • diracMatrixMatterAction (ActiveGauge.rotation x)
      (primalInsertion (weight x • primalUnrotation point spin color coefficient x)) =
    (nativeConfiguration signal).matter x+r • (weight x • diracMatrixMatterAction (ActiveGauge.rotation point)
      (primalInsertion (primalCoefficientForce spin color coefficient)))
  rw [insertion,matrixMatter_real_smul,primalUnrotation_physical]

private theorem nativeMatter_coordinates (signal : BasePoint → Field289) :
    (fun x => matterCoordinateEquiv ((nativeConfiguration signal).matter x)) =
      fun x => diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation x)
        (matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x)) := by
  funext x
  rw [nativeMatter_family_rotated,diracMatrixMatterCoordinateRealBilinear_apply]
  have value : matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x) =
      matterCoordinateEquiv (actual.matter 0+primalInsertion (signal x)) := by
    rw [map_add]
    rfl
  rw [value,LinearEquiv.symm_apply_apply]

private theorem nativeMatter_coordinates_differentiable (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) :
    DifferentiableAt ℝ (fun x => matterCoordinateEquiv ((nativeConfiguration signal).matter x)) point := by
  rw [nativeMatter_coordinates]
  have rotation : DifferentiableAt ℝ ActiveGauge.rotation point :=
    (rotation_source_smooth.differentiable (by simp)).differentiableAt
  have unrotated : DifferentiableAt ℝ (fun x => matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x)) point := by
    have derivative := (primalInsertionCLM.hasFDerivAt.comp point smooth.hasFDerivAt).const_add
      (matterCoordinateEquiv (actual.matter 0))
    change HasFDerivAt (fun x => matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x)) _ point at derivative
    exact derivative.differentiableAt
  exact (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.hasFDerivAt_of_bilinear
    rotation.hasFDerivAt unrotated.hasFDerivAt).differentiableAt

private theorem scalarMatterPoint (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (smooth : DifferentiableAt ℝ (fun x => matterCoordinateEquiv (configuration.matter x)) point)
    (direction : DiracExteriorMatterCarrier) (weight : BasePoint → ℝ)
    (weightSmooth : DifferentiableAt ℝ weight point) (r : ℝ) :
    toContinuumPointField { configuration with matter := fun x => configuration.matter x+r • (weight x • direction) } point =
      withMatterJets (toContinuumPointField configuration point)
        (configuration.matter point+r • (weight point • direction))
        (holonomicMatterCovariantDerivative configuration point+r •
          (fun mu => fieldDirectionalDerivative weight point mu • direction+
            weight point • holonomicMatterVariationAlgebraicDirection configuration (matterCoordinateEquiv direction) point mu)) := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  funext mu
  change holonomicMatterCovariantDerivative
    { configuration with matter := fun x => configuration.matter x+r • (weight x • direction) } point mu =
      holonomicMatterCovariantDerivative configuration point mu+r •
        (fieldDirectionalDerivative weight point mu • direction+weight point •
          holonomicMatterVariationAlgebraicDirection configuration (matterCoordinateEquiv direction) point mu)
  have coordinates : (fun x => matterCoordinateEquiv (configuration.matter x+r • (weight x • direction))) =
      fun x => matterCoordinateEquiv (configuration.matter x)+r • (weight x • matterCoordinateEquiv direction) := by
    funext x
    rw [map_add,primalInsertion_real_smul,primalInsertion_real_smul]
  have derivative := smooth.hasFDerivAt.add ((weightSmooth.hasFDerivAt.smul_const (matterCoordinateEquiv direction)).const_smul r)
  change HasFDerivAt (fun x => matterCoordinateEquiv (configuration.matter x)+r • (weight x • matterCoordinateEquiv direction)) _ point at derivative
  have differentiated : fieldDirectionalDerivative (fun x => matterCoordinateEquiv (configuration.matter x+r • (weight x • direction))) point mu =
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (configuration.matter x)) point mu+
        r • (fieldDirectionalDerivative weight point mu • matterCoordinateEquiv direction) := by
    rw [coordinates,fieldDirectionalDerivative,derivative.fderiv]
    simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,fieldDirectionalDerivative]
  unfold holonomicMatterCovariantDerivative holonomicMatterVariationAlgebraicDirection
  dsimp only
  rw [differentiated,map_add,matterCoordinateEquiv_symm_real_smul,matterCoordinateEquiv_symm_real_smul,
    LinearEquiv.symm_apply_apply,map_add,matrixMatter_real_smul,matrixMatter_real_smul,
    map_add,complexLinear_real_smul,complexLinear_real_smul]
  module

private theorem nativePrimal_weighted_point (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ)
    (weight : BasePoint → ℝ) (weightSmooth : DifferentiableAt ℝ weight point) (r : ℝ) :
    nativePoint (fun x => signal x+r • (weight x • primalUnrotation point spin color coefficient x)) point =
      withMatterJets (nativePoint signal point)
        ((nativePoint signal point).matter+r • (weight point • diracMatrixMatterAction (ActiveGauge.rotation point)
          (primalInsertion (primalCoefficientForce spin color coefficient))))
        ((nativePoint signal point).matterCovariantDerivative+r •
          (fun mu => fieldDirectionalDerivative weight point mu • diracMatrixMatterAction (ActiveGauge.rotation point)
              (primalInsertion (primalCoefficientForce spin color coefficient))+
            weight point • holonomicMatterVariationAlgebraicDirection (nativeConfiguration signal)
              (matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point)
                (primalInsertion (primalCoefficientForce spin color coefficient)))) point mu)) := by
  unfold nativePoint
  rw [nativePrimal_fixed_configuration]
  exact scalarMatterPoint (nativeConfiguration signal) point (nativeMatter_coordinates_differentiable signal point smooth)
    _ weight weightSmooth r

private def primalPhysicalDirection (point : BasePoint) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point)
    (primalInsertion (primalCoefficientForce spin color coefficient)))

private theorem nativePrimal_value_curve (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) :
    (fun r : ℝ => nativeDensity (fun x => signal x+r • primalUnrotation point spin color coefficient x) point) =
      motherPrimalAlgebraicCurve signal point (primalPhysicalDirection point spin color coefficient) := by
  funext r
  unfold nativeDensity motherPrimalAlgebraicCurve motherPrimalCurve primalPhysicalDirection
  have varied := nativePrimal_weighted_point signal point smooth spin color coefficient (fun _ => 1) (differentiableAt_const 1) r
  simp only [one_smul] at varied
  rw [varied]
  have slope : (fun mu => fieldDirectionalDerivative (fun _ : BasePoint => (1 : ℝ)) point mu •
      diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion (primalCoefficientForce spin color coefficient))+
      holonomicMatterVariationAlgebraicDirection (nativeConfiguration signal)
        (matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point)
          (primalInsertion (primalCoefficientForce spin color coefficient)))) point mu) =
      pointwiseMatterVariationAlgebraicDirection (nativeActionJet signal point).gravityConnection
        (nativeActionJet signal point).p286GaugeConnection
        (matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point)
          (primalInsertion (primalCoefficientForce spin color coefficient)))) := by
    funext mu
    simp only [fieldDirectionalDerivative,(hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) point).fderiv,zero_apply,matterRealZero,zero_add]
    rfl
  rw [slope,LinearEquiv.symm_apply_apply]
  rfl

private def primalCoordinateWeight (point : BasePoint) (mu : Fin 4) (position : BasePoint) : ℝ := position mu-point mu

private theorem primalCoordinateWeight_first (point : BasePoint) (mu nu : Fin 4) :
    fieldDirectionalDerivative (primalCoordinateWeight point mu) point nu = if nu=mu then 1 else 0 := by
  have source := ((EuclideanSpace.proj mu : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).sub_const (point mu)
  change HasFDerivAt (primalCoordinateWeight point mu) _ point at source
  rw [fieldDirectionalDerivative,source.fderiv]
  simp [coordinateDirection,eq_comm]

private theorem nativePrimal_momentum_curve (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) (mu : Fin 4) :
    (fun r : ℝ => nativeDensity (fun x => signal x+r •
      (primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x)) point) =
      motherPrimalMomentumCurve signal point (primalPhysicalDirection point spin color coefficient) mu := by
  funext r
  have weightSmooth : DifferentiableAt ℝ (primalCoordinateWeight point mu) point :=
    ((EuclideanSpace.proj mu : BasePoint →L[ℝ] ℝ).differentiableAt.sub_const (point mu))
  unfold nativeDensity motherPrimalMomentumCurve motherPrimalCurve primalPhysicalDirection
  rw [nativePrimal_weighted_point signal point smooth spin color coefficient _ weightSmooth r]
  have weightValue : primalCoordinateWeight point mu point=0 := by simp [primalCoordinateWeight]
  rw [weightValue]
  have realZero (v : DiracExteriorMatterCarrier) : (0 : ℝ) • v=0 := by
    change (0 : ℂ) • v=0
    exact zero_smul ℂ v
  simp only [realZero,add_zero,LinearEquiv.symm_apply_apply]
  congr 1
  congr 1
  funext nu
  simp only [Pi.add_apply,Pi.smul_apply]
  rw [primalCoordinateWeight_first]
  by_cases same : nu=mu
  · simp [same]
  · simp [same,realZero]

private theorem primalMomentumVariation_firstJet (point : BasePoint) (spin : Fin 4) (color : Fin 3)
    (coefficient : ℂ) (mu : Fin 4) :
    signalFirstJet (fun x => primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x) point =
      (0,Pi.single mu (primalCoefficientForce spin color coefficient)) := by
  have weight := ((EuclideanSpace.proj mu : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).sub_const (point mu)
  change HasFDerivAt (primalCoordinateWeight point mu) _ point at weight
  have unrotation := ((primalUnrotation_smooth point spin color coefficient).differentiable (by simp)).differentiableAt.hasFDerivAt (x := point)
  have source := weight.smul unrotation
  change HasFDerivAt (fun x => primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x) _ point at source
  apply Prod.ext
  · simp [signalFirstJet,primalCoordinateWeight]
  · funext nu
    change fieldDirectionalDerivative (fun x => primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x) point nu =
      (Pi.single mu (primalCoefficientForce spin color coefficient) : Fin 4 → Field289) nu
    rw [fieldDirectionalDerivative,source.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply,primalCoordinateWeight,sub_self,
      zero_smul,zero_add,primalUnrotation_value]
    simp [coordinateDirection,Pi.single_apply,eq_comm]

private theorem primalMomentumVariation_differentiable (point : BasePoint) (spin : Fin 4) (color : Fin 3)
    (coefficient : ℂ) (mu : Fin 4) :
    DifferentiableAt ℝ (fun x => primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x) point := by
  exact ((EuclideanSpace.proj mu : BasePoint →L[ℝ] ℝ).differentiableAt.sub_const (point mu)).smul
    ((primalUnrotation_smooth point spin color coefficient).differentiable (by simp) |>.differentiableAt)

private theorem nativePrimal_momentum_generated (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : DifferentiableAt ℝ signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) (mu : Fin 4) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,Pi.single mu (primalCoefficientForce spin color coefficient)) =
      matterDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal)
        (primalPhysicalDirection point spin color coefficient) mu point := by
  have generated := nativeDensity_variation_generated signal
    (fun x => primalCoordinateWeight point mu x • primalUnrotation point spin color coefficient x) point smooth
    (primalMomentumVariation_differentiable point spin color coefficient mu) inside
  rw [primalMomentumVariation_firstJet,nativePrimal_momentum_curve signal point smooth] at generated
  exact generated.unique (motherPrimalMomentumCurve_generated signal point (primalPhysicalDirection point spin color coefficient) mu)

private theorem flux_direction (signal variation : BasePoint → Field289) (point : BasePoint) (mu : Fin 4) :
    nativeVariationFlux signal variation mu point =
      fderiv ℝ nativeJetDensity (signalFirstJet signal point) (0,Pi.single mu (variation point)) := by
  have reconstruction : (0,Pi.single mu (variation point)) =
      ∑ field : Fin 289,variation point field • nativeJetBasis (some mu,field) := by
    apply Prod.ext
    · simp [nativeJetBasis,Prod.fst_sum]
    · funext nu field
      by_cases same : nu=mu
      · subst nu
        simp [nativeJetBasis,Prod.snd_sum,Finset.sum_apply,Pi.single_apply,mul_ite]
      · simp [nativeJetBasis,Prod.snd_sum,Finset.sum_apply,same]
  rw [reconstruction]
  simp only [map_sum,map_smul,smul_eq_mul,nativeVariationFlux,nativeSignalMomentum]
  apply Finset.sum_congr rfl
  intro field _
  exact mul_comm _ _

private theorem primalPhysicalDirection_constant (anchor position : BasePoint) (spin : Fin 4) (color : Fin 3)
    (coefficient : ℂ) :
    primalPhysicalDirection position spin color
      (inversePhaseComponent position spin*phaseComponents anchor spin*coefficient) =
      primalPhysicalDirection anchor spin color coefficient := by
  unfold primalPhysicalDirection
  exact congrArg matterCoordinateEquiv (primalUnrotation_physical anchor position spin color coefficient)

private theorem nativePrimal_flux_generated (signal : BasePoint → Field289) (anchor position : BasePoint)
    (smooth : DifferentiableAt ℝ signal position) (inside : signalFirstJet signal position ∈ nativeEulerSourceDomain)
    (spin : Fin 4) (color : Fin 3) (coefficient : ℂ) (mu : Fin 4) :
    nativeVariationFlux signal (primalUnrotation anchor spin color coefficient) mu position =
      matterDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal)
        (primalPhysicalDirection anchor spin color coefficient) mu position := by
  rw [flux_direction]
  unfold primalUnrotation
  rw [nativePrimal_momentum_generated signal position smooth inside,primalPhysicalDirection_constant]

private theorem primalSignal_near (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain) :
    ∀ᶠ position in 𝓝 point,DifferentiableAt ℝ signal position ∧ signalFirstJet signal position ∈ nativeEulerSourceDomain := by
  have smoothNear : ∀ᶠ position in 𝓝 point,ContDiffAt ℝ 2 signal position := smooth.eventually (by simp)
  have density : ContDiffAt ℝ 2 nativeJetDensity (signalFirstJet signal point) := inside
  have domain : ∀ᶠ jet in 𝓝 (signalFirstJet signal point),jet ∈ nativeEulerSourceDomain := density.eventually (by simp)
  have near := (signalFirstJet_source_smooth signal point smooth).continuousAt.tendsto.eventually domain
  filter_upwards [smoothNear,near] with position regular present
  exact ⟨regular.differentiableAt (by norm_num),present⟩

/-- The inverse rotation is generated from the actual source phase, so its derivative contribution is retained in the same flux. -/
theorem nativePrimalEuler_slot_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    nativeHolonomicEuler signal point (primalSlot part spin color) =
      (nativeEuler signal point).matter (matterCoordinateEquiv
        (diracMatrixMatterAction (ActiveGauge.rotation point)
          (primalInsertion (Pi.single (primalSlot part spin color) 1)))) := by
  let variation := primalUnrotation point spin color (primalPartCoefficient part)
  let direction := primalPhysicalDirection point spin color (primalPartCoefficient part)
  have variationSmooth : DifferentiableAt ℝ variation point :=
    ((primalUnrotation_smooth point spin color (primalPartCoefficient part)).differentiable (by simp)).differentiableAt
  have mother := nativeDensity_variation_euler signal variation point smooth variationSmooth inside
  have curve : (fun r : ℝ => nativeDensity (fun x => signal x+r • variation x) point) =
      motherPrimalAlgebraicCurve signal point direction :=
    nativePrimal_value_curve signal point (smooth.differentiableAt (by norm_num)) _ _ _
  rw [curve,(motherPrimalAlgebraicCurve_generated signal point direction).deriv] at mother
  have value : variation point=Pi.single (primalSlot part spin color) 1 := by
    change primalUnrotation point spin color (primalPartCoefficient part) point=Pi.single (primalSlot part spin color) 1
    rw [primalUnrotation_value,primalCoefficientForce_unit]
  have flux (mu : Fin 4) : nativeVariationFlux signal variation mu =ᶠ[𝓝 point]
      matterDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu := by
    filter_upwards [primalSignal_near signal point smooth inside] with position regular
    exact nativePrimal_flux_generated signal point position regular.1 regular.2 _ _ _ mu
  have divergence : (∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) point mu) =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource (nativeConfiguration signal) direction point := by
    unfold matterDifferentialMomentumDivergence
    apply Finset.sum_congr rfl
    intro mu _
    unfold fieldDirectionalDerivative
    rw [(flux mu).fderiv_eq (𝕜 := ℝ)]
  rw [value,divergence] at mother
  simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Fintype.sum_ite_eq'] at mother
  have residual := motherPrimalEuler_action signal point direction
  have algebraic : deriv (motherPrimalAlgebraicCurve signal point direction) 0 =
      pointwiseDiracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource point (nativeActionJet signal point) direction :=
    (motherPrimalAlgebraicCurve_generated signal point direction).deriv
  rw [algebraic] at residual
  simp_rw [(motherPrimalMomentumCurve_generated signal _ direction _).deriv] at residual
  change (nativeEuler signal point).matter direction=
    pointwiseDiracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource point (nativeActionJet signal point) direction-
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource (nativeConfiguration signal) direction point at residual
  have identified : nativeHolonomicEuler signal point (primalSlot part spin color)=(nativeEuler signal point).matter direction := by
    linarith
  unfold direction primalPhysicalDirection at identified
  rw [primalCoefficientForce_unit] at identified
  exact identified

theorem nativePrimalEuler_identification (signal : BasePoint → Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point ∈ nativeEulerSourceDomain)
    (field : Fin 289) (range : 73 ≤ field.val ∧ field.val < 97) :
    nativeHolonomicEuler signal point field =
      (nativeEuler signal point).matter (matterCoordinateEquiv
        (diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion (Pi.single field 1)))) := by
  let part : Fin 2 := ⟨(field.val-73)/12,by omega⟩
  let spin : Fin 4 := ⟨((field.val-73)%12)/3,by omega⟩
  let color : Fin 3 := ⟨(field.val-73)%3,by omega⟩
  have original : primalSlot part spin color=field := by
    apply Fin.ext
    simp only [primalSlot,part,spin,color,Fin.val_mk]
    omega
  simpa only [original] using nativePrimalEuler_slot_identification signal point smooth inside part spin color

end LowEnergy.SourcePropagationMotherResidualDirections
