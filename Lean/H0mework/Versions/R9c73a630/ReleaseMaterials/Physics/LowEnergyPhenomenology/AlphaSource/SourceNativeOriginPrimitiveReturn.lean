import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginMatterPhase

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeOriginPhaseWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair StageNineLorentzConnectionVariation StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open PreparationPhysicalNativePoleChargeReturn PreparationVacuumOriginalGreenFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeFieldInjection PreparationVacuumNativeSourceRestriction
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift GaussNativeMatter
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourcePropagationNativeActionHessian SourceQuantumScalarChart PreparationVacuumLowerClassical
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourceOriginGaugePrimitive : StageNineHolonomicConfiguration :=
  colorPrimitiveDirection 2 (fun _=>-1) (fun _=>0) actual

/-- The same original color-gauge direction is completed by its source-generated matter phase, including the independent dual. -/
def sourceOriginGaugePhasePrimitive : StageNineHolonomicConfiguration :=
  { sourceOriginGaugePrimitive with
    matter:=fun point=>sourceNativeOriginGenerator (actual.matter point)
    conjugateMatter:=fun point=>-(actual.conjugateMatter point).comp sourceNativeOriginGenerator }

theorem sourceOriginPrimitive_matter (point : BasePoint) :
    sourceOriginGaugePhasePrimitive.matter point=
      sourceOriginGaugePrimitive.matter point-(Complex.I/2) • actual.matter point := by
  simp only [sourceOriginGaugePhasePrimitive,sourceNativeOriginGenerator,LinearMap.sub_apply,
    LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.id_apply,
    sourceOriginGaugePrimitive,colorPrimitiveDirection,nativeMother,colorLie,
    LinearEquiv.symm_apply_apply,Complex.ofReal_neg,Complex.ofReal_one]
  norm_num
  module

theorem sourceOriginPrimitive_dual (point : BasePoint) :
    sourceOriginGaugePhasePrimitive.conjugateMatter point=
      sourceOriginGaugePrimitive.conjugateMatter point+(Complex.I/2) • actual.conjugateMatter point := by
  apply LinearMap.ext
  intro v
  simp only [sourceOriginGaugePhasePrimitive,LinearMap.comp_apply,LinearMap.neg_apply,
    sourceNativeOriginGenerator,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
    map_sub,map_neg,map_smul,sourceOriginGaugePrimitive,colorPrimitiveDirection,nativeMother,colorLie,
    LinearEquiv.symm_apply_apply,Complex.ofReal_neg,Complex.ofReal_one,smul_eq_mul]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  norm_num only [neg_neg,one_smul]
  ring

private theorem gauge_scale : gaugeScale=2*sourceNativeOriginGaugeWeight := by
  unfold gaugeScale spinScale sourceNativeOriginGaugeWeight
  ring

def sourceOriginAuxiliaryWeight : ℝ := Real.sqrt 2*Real.sqrt 15/5

/-- The actual constitutive source fixes the auxiliary scale, independently of the matter-phase identification. -/
theorem sourceOriginAuxiliary_scale :
    gaugeScale^2/(sourceCoupling*lapse)=2*sourceOriginAuxiliaryWeight := by
  have g : gaugeScale^2=(18/25:ℝ) := by
    unfold gaugeScale
    rw [div_pow,mul_pow,spinScale_sq]
    norm_num
  have a : sourceOriginAuxiliaryWeight^2=(6/5:ℝ) := by
    unfold sourceOriginAuxiliaryWeight
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt (by norm_num)]
    norm_num
  have positive : 0<sourceOriginAuxiliaryWeight := by unfold sourceOriginAuxiliaryWeight;positivity
  have productSquared : (sourceOriginAuxiliaryWeight*lapse)^2=(324/625:ℝ) := by
    rw [mul_pow,a,lapse_sq]
    norm_num
  have product : sourceOriginAuxiliaryWeight*lapse=18/25 := by
    nlinarith [mul_pos positive lapse_pos]
  rw [sourceCoupling_eq]
  apply (div_eq_iff (mul_ne_zero (by norm_num) lapse_pos.ne')).2
  rw [g]
  nlinarith [product]

theorem sourceOriginPrimitive_gauge (point : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal 0) mu)=
      sourceOriginGaugePhasePrimitive.gaugeConnection point mu := by
  rw [sourceNativeOriginReal_gauge]
  unfold sourceOriginGaugePhasePrimitive sourceOriginGaugePrimitive colorPrimitiveDirection gaugeDirection colorLie
  simp only [Pi.zero_apply,zero_smul,sub_zero,map_smul,p286CoordinateLieBracket,
    LinearEquiv.symm_apply_apply,actual_gaugeConnection]
  fin_cases mu <;>
    simp [gaugePotential,p286LieBracket_smul_right,sourceColorP286Generator_bracket,
      sourceNativeOrigin_unit_zero,sourceNativeOrigin_unit_one,gauge_scale,smul_smul]
  · simp [p286LieBracket,suLieBracket]
    rfl
  all_goals module

private theorem auxiliary_slot (pair : Fin 6) (a : Fin 12) :
    fieldGaugeB (sourceNativeOriginReal 0) pair a=
      if pair=0 ∧ a=0 then sourceOriginAuxiliaryWeight else
        if pair=1 ∧ a=1 then -sourceOriginAuxiliaryWeight else 0 := by
  have before (r : Fin 289) (small : r.val<217) : r≠gaugeBSlot pair a := by
    intro equal
    have value:=congrArg Fin.val equal
    simp only [gaugeBSlot,Fin.val_mk] at value
    omega
  have first : (217:Fin 289)=gaugeBSlot pair a ↔ pair=0 ∧ a=0 := by
    simp only [Fin.ext_iff,gaugeBSlot]
    omega
  have second : (230:Fin 289)=gaugeBSlot pair a ↔ pair=1 ∧ a=1 := by
    simp only [Fin.ext_iff,gaugeBSlot]
    omega
  simp only [fieldGaugeB,sourceNativeOriginReal,sourceNativeOriginAction_generated]
  norm_num [sourceNativeOriginActionTerms,sourceMatrix,SourceTerm.matrix,Powers.value,Matrix.single_apply,
    before 21 (by decide),before 34 (by decide),before 88 (by decide),before 94 (by decide),
    before 112 (by decide),before 118 (by decide),first,second,
    coefficientValue,rootTwo,rootFifteen,sourceOriginAuxiliaryWeight,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]
  split_ifs <;> first | omega | (norm_num [Complex.mul_re,Complex.mul_im] <;> ring)

theorem sourceOriginPrimitive_auxiliary (point : BasePoint) (pair : Fin 6) :
    gaugeBInsertion (sourceNativeOriginReal 0) pair=sourceOriginGaugePhasePrimitive.gaugeAuxiliary point pair := by
  have zeroBracket : p286LieBracket (sourceColorP286Generator 2) 0=0 := by
    simpa only [zero_smul] using p286LieBracket_smul_right 0 0 (sourceColorP286Generator 2)
  unfold gaugeBInsertion
  simp_rw [auxiliary_slot]
  unfold sourceOriginGaugePhasePrimitive sourceOriginGaugePrimitive colorPrimitiveDirection
  rw [actual_gaugeAuxiliary]
  fin_cases pair <;>
    simp [electricAuxiliary,sourceOriginAuxiliary_scale,sourceNativeOrigin_unit_zero,sourceNativeOrigin_unit_one,
      sourceColorP286Generator_bracket,p286LieBracket_smul_right,map_smul,map_neg,smul_smul,zeroBracket]
  all_goals module

private theorem auxiliary_geometry_zero (i : Fin 289) (lo : (145 : ℕ) ≤ i.val) (hi : i.val < (217 : ℕ)) :
    sourceNativeOriginReal 0 i=0 := by
  unfold sourceNativeOriginReal
  rw [sourceNativeOriginAction_generated]
  dsimp only []
  have row (a : Fin 289) (outside : a.val<145 ∨ 217≤a.val) : a≠i := by
    intro equal
    have := congrArg Fin.val equal
    omega
  norm_num [sourceNativeOriginActionTerms,sourceMatrix,SourceTerm.matrix,Powers.value,
    Matrix.single_apply,show (21:Fin 289)≠i from row 21 (by decide),
    show (34:Fin 289)≠i from row 34 (by decide),
    show (88:Fin 289)≠i from row 88 (by decide),show (94:Fin 289)≠i from row 94 (by decide),
    show (112:Fin 289)≠i from row 112 (by decide),show (118:Fin 289)≠i from row 118 (by decide),
    show (217:Fin 289)≠i from row 217 (by decide),show (230:Fin 289)≠i from row 230 (by decide)]

/-- The complete geometric and scalar components agree with the same original primitive. -/
theorem sourceOriginPrimitive_remaining (point : BasePoint) :
    fieldCoframe (sourceNativeOriginReal 0)=sourceOriginGaugePhasePrimitive.coframe point ∧
    lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (sourceNativeOriginReal 0))=
      sourceOriginGaugePhasePrimitive.gravityConnection point ∧
    fieldGravityB (sourceNativeOriginReal 0)=sourceOriginGaugePhasePrimitive.gravityAuxiliary point ∧
    fieldMultiplier (sourceNativeOriginReal 0)=sourceOriginGaugePhasePrimitive.gravitySimplicityMultiplier point ∧
    fieldScalar (sourceNativeOriginReal 0)=sourceOriginGaugePhasePrimitive.scalar point := by
  have fields:=sourceNativeOriginReal_remaining 0
  refine ⟨fields.2.1,?_,?_,?_,?_⟩
  · rw [fields.2.2]
    ext mu a b
    simp [lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix,
      sourceOriginGaugePhasePrimitive,sourceOriginGaugePrimitive,colorPrimitiveDirection]
  · funext pair a
    apply auxiliary_geometry_zero
    all_goals simp only [gravitySlot,Fin.val_mk];omega
  · funext pair a
    apply auxiliary_geometry_zero
    all_goals simp only [multiplierSlot,Fin.val_mk];omega
  · rw [fields.1]
    change 0=scalarDirection 2 (-1) (actual.scalar point)
    rw [actual_scalar]
    exact (scalarDirection_vacuum 2 (-1)).symm

private theorem primal_smul (r : ℝ) (f : Field289) : primalInsertion (r • f)=r • primalInsertion f := by
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldPrimalComplex (r • f) spin color=r • fieldPrimalComplex f spin color := by
    simp [fieldPrimalComplex,fieldPrimal,Complex.real_smul,Complex.ofReal_mul]
    ring
  simp only [primalInsertion,coefficients,Complex.real_smul,mul_smul,←Finset.smul_sum]
  rfl

private theorem dual_smul (r : ℝ) (f : Field289) : dualInsertion (r • f)=r • dualInsertion f := by
  apply LinearMap.ext
  intro v
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldDualComplex (r • f) spin color=r • fieldDualComplex f spin color := by
    simp [fieldDualComplex,fieldDual,Complex.real_smul,Complex.ofReal_mul]
    ring
  change (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex (r • f) spin color*sourceTripletRead (v spin) color)=
    r • (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex f spin color*sourceTripletRead (v spin) color)
  simp only [coefficients,smul_mul_assoc,←Finset.smul_sum]

private theorem auxiliary_smul (r : ℝ) (f : Field289) (pair : Fin 6) :
    gaugeBInsertion (r • f) pair=r • gaugeBInsertion f pair := by
  simp only [gaugeBInsertion,fieldGaugeB,Pi.smul_apply,smul_eq_mul,mul_smul,←Finset.smul_sum,map_smul]

/-- The full source ray is the original gauge-plus-phase variation at every actual spacetime point. -/
theorem sourceNativeOrigin_configuration (r : ℝ) :
    nativeConfiguration (fun _=>r • sourceNativeOriginReal 0)=
      configurationRay actual sourceOriginGaugePhasePrimitive r := by
  apply StageNineHolonomicConfiguration.ext <;> funext point
  all_goals simp only [nativeConfiguration,configurationRay]
  · rw [←(sourceOriginPrimitive_remaining point).1]
    rfl
  · rw [←(sourceOriginPrimitive_remaining point).2.1]
    congr 1
    ext mu a b
    simp [fieldLorentz,lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix]
    simp only [Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [←(sourceOriginPrimitive_remaining point).2.2.1]
    rfl
  · rw [←(sourceOriginPrimitive_remaining point).2.2.2.1]
    rfl
  · funext mu
    rw [fieldGauge_smul,map_smul,sourceOriginPrimitive_gauge]
  · funext pair
    rw [auxiliary_smul,sourceOriginPrimitive_auxiliary]
  · rw [fieldScalar_smul,(sourceOriginPrimitive_remaining point).2.2.2.2]
  · rw [primal_smul,LinearMap.map_smul_of_tower,sourceNativeOrigin_actualMatter]
    rfl
  · rw [dual_smul,LinearMap.smul_comp,sourceNativeOrigin_actualDual]
    rfl


/-- The full endpoint's action direction is the same original color primitive; its phase acts on the independently retained external legs. -/
theorem sourceNativeOrigin_actionDirection :
    fieldDirection (sourceNativeOriginReal 0)=
      PreparationVacuumNativeLocalWard.stateVariation (Fin.castAdd 6 (2:Fin 3)) (-1) 0
        (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val) := by
  have primitive:=nativeSourcePrimitive_state (Fin.castAdd 6 (2:Fin 3)) (-1) 0
  simp only [nativeSourcePrimitive,Fin.addCases_left] at primitive
  rw [←primitive]
  rw [sourceNativeOriginAction_state]
  unfold configurationState
  refine Prod.ext ?_ ?_
  · rfl
  apply Prod.ext
  · funext mu
    dsimp only []
    rw [originalConnection_source]
    change sourceNativeOriginConnection 0 mu=
      spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu)+
        GaussNativeMatter.nativePrimal (p286CoordinateEquiv (sourceOriginGaugePhasePrimitive.gaugeConnection 0 mu))
    rw [←sourceOriginPrimitive_gauge,LinearEquiv.apply_symm_apply,sourceNativeOriginReal_gauge]
    simp [sourceNativeOriginConnection,PointwiseDiracSpinConnectionLift.diracSpinConnectionLift]
    split_ifs <;> simp only [map_zero]
  · change 0=PreparationVacuumGaugeSourceInjection.scalarLinear (scalarDirection 2 (-1) (actual.scalar 0))
    have zero : scalarDirection 2 (-1) (actual.scalar 0)=0 := by
      rw [actual_scalar]
      exact scalarDirection_vacuum 2 (-1)
    rw [zero,map_zero]

end LowEnergy.PreparationPhysicalNativeOriginPhaseWard
