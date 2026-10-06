import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveLorentzFields

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSourceRestriction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRepresentation SU7ExteriorYukawaMassSpectrum SU7ExteriorMatterRestriction
open FullQuantum.StateGreen FullQuantum.CoframeResponse SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert GaussHistoryHilbert GaussNativeMatter
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical PreparationCoordinates
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalDensity
open scoped BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- Read the primitive fields from the actual source, retaining all70 scalar coordinates. -/
def originalSourceData : FieldData:=
  (actual.scalar 0,(fun mu=>p286CoordinateEquiv (actual.gaugeConnection 0 mu)),
    actual.coframe 0,(fun mu a=>loweredLorentzConnectionCoefficient (actual.gravityConnection 0) mu a))

theorem originalSourceData_state : stateDirectionMap originalSourceData=sourceState sourcePoint.val :=by
  rw [←configurationState_emitter]
  apply Prod.ext
  · exact (emitted_source_coframe).symm
  apply Prod.ext
  · funext mu
    change spinLinear mu originalSourceData.2.2.2+nativePrimal (originalSourceData.2.1 mu)=Quantum.operatorMatrix (FullQuantum.connection (emitter sourcePoint.val) 0 mu)
    rw [originalConnection_source]
    change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
      (fun nu a=>loweredLorentzConnectionCoefficient (actual.gravityConnection 0) nu a)) mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (actual.gaugeConnection 0 mu))=
      spinCoordinates (diracSpinConnectionLift (actual.gravityConnection 0) mu)+
        nativePrimal (show NativeLie from p286CoordinateEquiv ((emitter sourcePoint.val).gaugeConnection 0 mu))
    rw [emitted_source_gauge]
    congr 2
    simp only [diracSpinConnectionLift,loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  · change scalarLinear (actual.scalar 0)=scalarLinear ((emitter sourcePoint.val).scalar 0)
    rw [emitted_source_scalar]

def nativeSourcePrimitive (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) : StageNineHolonomicConfiguration:=
  Fin.addCases (fun g : Fin 3=>colorPrimitiveDirection g (fun _=>theta) (fun _=>gradient) actual)
    (fun a : Fin 6=>lorentzPrimitiveDirection a (fun _=>theta) (fun _=>gradient)
      actual (fun _=>originalSourceData)) n

theorem nativeSourcePrimitive_scalar (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) :
    (nativeSourcePrimitive n theta gradient).scalar 0=0 :=by
  refine Fin.addCases (motive:=fun n : Fin 9=>(nativeSourcePrimitive n theta gradient).scalar 0=0)
    (fun g : Fin 3=>?_) (fun a : Fin 6=>?_) n
  · simp only [nativeSourcePrimitive,Fin.addCases_left,colorPrimitiveDirection]
    rw [actual_scalar]
    exact scalarDirection_vacuum g theta
  · simp only [nativeSourcePrimitive,Fin.addCases_right,lorentzPrimitiveDirection,Pi.zero_apply]

/-- The original three exterior color basis legs; they are coordinate restrictions of the whole matter carrier. -/
def sourceTripletIndex (color : Fin 3) : ExteriorBasisIndex 2:=
  ⟨{Sum.inl color,hyperPlusIndex},by simp [hyperPlusIndex]⟩

def sourceTripletMatter (color : Fin 3) : SU7ExteriorSpinorMatterCarrier:=
  (0,su7ExteriorBasis 2 (sourceTripletIndex color),0)

def sourceTripletRead (matter : SU7ExteriorSpinorMatterCarrier) (color : Fin 3) : ℂ:=
  (su7ExteriorBasis 2).repr matter.2.1 (sourceTripletIndex color)

def sourceTripletLeg (spin : Fin 4) (color : Fin 3) : DiracExteriorMatterCarrier:=
  Pi.single spin (sourceTripletMatter color)

private def realPart (part : Fin 2) (value : ℂ) : ℝ:=Fin.cases value.re (fun _=>value.im) part

/-- The literal nonscalar289 slots read the original configuration, including its independent linear dual and both BF fields. -/
def nonscalarRestriction (c : StageNineHolonomicConfiguration) (slot : Fin 289) : ℝ:=
  Fin.addCases (motive:=fun _=>ℝ) (fun _ : Fin 9=>0) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 48=>rawCoordinates (show NativeLie from p286CoordinateEquiv
      (c.gaugeConnection 0 (i.divNat (m:=4) (n:=12)))) (i.modNat (m:=4) (n:=12))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 16=>c.coframe 0 (i.divNat (m:=4) (n:=4)) (i.modNat (m:=4) (n:=4))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 24=>realPart (i.divNat (m:=2) (n:=12))
      (sourceTripletRead (c.matter 0 ((i.modNat (m:=2) (n:=12)).divNat (m:=4) (n:=3))) ((i.modNat (m:=2) (n:=12)).modNat (m:=4) (n:=3)))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 24=>realPart (i.divNat (m:=2) (n:=12))
      (c.conjugateMatter 0 (sourceTripletLeg ((i.modNat (m:=2) (n:=12)).divNat (m:=4) (n:=3)) ((i.modNat (m:=2) (n:=12)).modNat (m:=4) (n:=3))))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 24=>loweredLorentzConnectionCoefficient (c.gravityConnection 0) (i.divNat (m:=4) (n:=6)) (i.modNat (m:=4) (n:=6))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 36=>c.gravityAuxiliary 0 (i.divNat (m:=6) (n:=6)) (i.modNat (m:=6) (n:=6))) (Fin.addCases (motive:=fun _=>ℝ)
    (fun i : Fin 36=>c.gravitySimplicityMultiplier 0 (i.divNat (m:=6) (n:=6)) (i.modNat (m:=6) (n:=6)))
    (fun i : Fin 72=>rawCoordinates (show NativeLie from p286CoordinateEquiv
      (c.gaugeAuxiliary 0 (i.divNat (m:=6) (n:=12)))) (i.modNat (m:=6) (n:=12)))))))))) slot

def nativeSourceColumn (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) : Field289:=
  nonscalarRestriction (nativeSourcePrimitive n theta gradient)

theorem nativeSourcePrimitive_state (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) :
    configurationState (nativeSourcePrimitive n theta gradient) 0=
      stateVariation n theta gradient (sourceState sourcePoint.val) :=by
  refine Fin.addCases (motive:=fun n : Fin 9=>configurationState (nativeSourcePrimitive n theta gradient) 0=
    stateVariation n theta gradient (sourceState sourcePoint.val)) (fun g : Fin 3=>?_) (fun a : Fin 6=>?_) n
  · simp only [nativeSourcePrimitive,Fin.addCases_left]
    rw [colorPrimitive_state]
    have original:=configurationState_emitter sourcePoint.val
    have source : configurationState actual 0=sourceState sourcePoint.val:=by
      rw [←original]
      apply Prod.ext
      · exact emitted_source_coframe.symm
      apply Prod.ext
      · funext mu
        change Quantum.operatorMatrix (FullQuantum.connection actual 0 mu)=Quantum.operatorMatrix (FullQuantum.connection (emitter sourcePoint.val) 0 mu)
        unfold FullQuantum.connection
        rw [emitted_source_gauge]
        rfl
      · change scalarLinear (actual.scalar 0)=scalarLinear ((emitter sourcePoint.val).scalar 0)
        rw [emitted_source_scalar]
    rw [source]
  · simp only [nativeSourcePrimitive,Fin.addCases_right]
    rw [lorentzPrimitive_state,configurationFromFields_state,originalSourceData_state]

theorem nonscalarRestriction_scalar (c : StageNineHolonomicConfiguration) (j : Fin 9) :
    nonscalarRestriction c (scalarSlot j)=0 :=by
  fin_cases j <;> rfl

theorem nonscalarRestriction_gauge (c : StageNineHolonomicConfiguration) (mu : Fin 4) (a : Fin 12) :
    nonscalarRestriction c (gaugeSlot mu a)=
      rawCoordinates (show NativeLie from p286CoordinateEquiv (c.gaugeConnection 0 mu)) a :=by
  fin_cases mu <;> fin_cases a <;> rfl

theorem nonscalarRestriction_coframe (c : StageNineHolonomicConfiguration) (a mu : Fin 4) :
    nonscalarRestriction c (coframeSlot a mu)=c.coframe 0 a mu :=by
  fin_cases a <;> fin_cases mu <;> rfl

theorem nonscalarRestriction_lorentz (c : StageNineHolonomicConfiguration) (mu : Fin 4) (a : Fin 6) :
    nonscalarRestriction c (lorentzSlot mu a)=loweredLorentzConnectionCoefficient (c.gravityConnection 0) mu a :=by
  fin_cases mu <;> fin_cases a <;> rfl

theorem nonscalarRestriction_primal (c : StageNineHolonomicConfiguration) (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    nonscalarRestriction c (primalSlot part spin color)=realPart part (sourceTripletRead (c.matter 0 spin) color) :=by
  fin_cases part <;> fin_cases spin <;> fin_cases color <;> rfl

theorem nonscalarRestriction_dual (c : StageNineHolonomicConfiguration) (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    nonscalarRestriction c (dualSlot part spin color)=realPart part (c.conjugateMatter 0 (sourceTripletLeg spin color)) :=by
  fin_cases part <;> fin_cases spin <;> fin_cases color <;> rfl

theorem nonscalarRestriction_gravity (c : StageNineHolonomicConfiguration) (i p : Fin 6) :
    nonscalarRestriction c (gravitySlot i p)=c.gravityAuxiliary 0 i p :=by
  fin_cases i <;> fin_cases p <;> rfl

theorem nonscalarRestriction_multiplier (c : StageNineHolonomicConfiguration) (i p : Fin 6) :
    nonscalarRestriction c (multiplierSlot i p)=c.gravitySimplicityMultiplier 0 i p :=by
  fin_cases i <;> fin_cases p <;> rfl

theorem nonscalarRestriction_gaugeB (c : StageNineHolonomicConfiguration) (pair : Fin 6) (a : Fin 12) :
    nonscalarRestriction c (gaugeBSlot pair a)=
      rawCoordinates (show NativeLie from p286CoordinateEquiv (c.gaugeAuxiliary 0 pair)) a :=by
  fin_cases pair <;> fin_cases a <;> rfl

private theorem originalGauge_basis (A : NativeLie) :
    (∑a : Fin 12,rawCoordinates A a • originalUnit a)=A :=by
  apply rawCoordinates.injective
  ext i
  simp only [map_sum,map_smul,originalUnit,LinearEquiv.apply_symm_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp [Pi.single_apply]

theorem nonscalarRestriction_fieldGauge (c : StageNineHolonomicConfiguration) (mu : Fin 4) :
    fieldGauge (nonscalarRestriction c) mu=p286CoordinateEquiv (c.gaugeConnection 0 mu) :=by
  simp only [fieldGauge,nonscalarRestriction_gauge]
  exact originalGauge_basis _

theorem nonscalarRestriction_fieldScalar (c : StageNineHolonomicConfiguration) :
    fieldScalar (nonscalarRestriction c)=0 :=by
  simp only [fieldScalar,nonscalarRestriction_scalar,zero_smul,Finset.sum_const_zero]

private theorem nonscalarRestriction_state (c : StageNineHolonomicConfiguration) (scalarZero : c.scalar 0=0) :
    fieldDirection (nonscalarRestriction c)=configurationState c 0 :=by
  rw [←stateDirection_source]
  apply Prod.ext
  · funext a mu
    exact nonscalarRestriction_coframe c a mu
  apply Prod.ext
  · funext mu
    change spinLinear mu (fieldLorentz (nonscalarRestriction c))+
      nativePrimal (fieldGauge (nonscalarRestriction c) mu)=Quantum.operatorMatrix (FullQuantum.connection c 0 mu)
    rw [originalConnection_source,nonscalarRestriction_fieldGauge]
    apply congrArg (fun M : SourceMatrix=>M+nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection 0 mu)))
    change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
      (fieldLorentz (nonscalarRestriction c))) mu)=spinCoordinates (diracSpinConnectionLift (c.gravityConnection 0) mu)
    apply congrArg spinCoordinates
    simp only [diracSpinConnectionLift,loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      fieldLorentz,nonscalarRestriction_lorentz]
  · change scalarLinear (fieldScalar (nonscalarRestriction c))=scalarLinear (c.scalar 0)
    rw [nonscalarRestriction_fieldScalar,scalarZero]

theorem nativeSourceColumn_state (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) :
    fieldDirection (nativeSourceColumn n theta gradient)=
      stateVariation n theta gradient (sourceState sourcePoint.val) :=by
  rw [nativeSourceColumn,nonscalarRestriction_state _ (nativeSourcePrimitive_scalar n theta gradient),
    nativeSourcePrimitive_state]

theorem nativeSourceColumn_Hamiltonian_generated (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (sourceState sourcePoint.val+
      r • fieldDirection (nativeSourceColumn n theta gradient)))
      (nativeFirst n theta gradient p (sourceState sourcePoint.val)) 0 :=by
  rw [nativeSourceColumn_state]
  exact nativeFirst_generated n theta gradient p sourcePoint

theorem nativeSourceColumn_rawAction (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    nativeRaw n theta gradient p (sourceState sourcePoint.val)=
      rawActionSymbol (nativeSourceColumn n theta gradient) p (sourceState sourcePoint.val) :=by
  exact nativeFirst_field_readback n theta gradient (nativeSourceColumn n theta gradient) p
    (sourceState sourcePoint.val) (nativeSourceColumn_state n theta gradient).symm
      ⟨coframe_nondegenerate sourcePoint,CanonicalGradedSpatialSource.temporal_noncharacteristic sourcePoint⟩

end LowEnergy.PreparationVacuumNativeSourceRestriction
