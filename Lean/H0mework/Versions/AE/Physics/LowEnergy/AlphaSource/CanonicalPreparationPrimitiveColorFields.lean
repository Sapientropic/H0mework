import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalGaugeScalar

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineHolonomicField DiracExteriorMatterAction DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7MotherGaugeTheory FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussNativeMatter
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection PreparationVacuumNativeLocalWard
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional

/-- The original independent momentum transforms by composition with the inverse generator. -/
def colorPrimitiveDirection (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration where
  coframe:=0
  gravityConnection:=0
  gravityAuxiliary:=0
  gravitySimplicityMultiplier:=0
  gaugeConnection x mu:=p286CoordinateEquiv.symm
    (gaugeDirection g (theta x) (parameterDerivative x)
      (fun nu=>show NativeLie from p286CoordinateEquiv (c.gaugeConnection x nu)) mu)
  gaugeAuxiliary x pair:=(theta x) • p286LieBracket (Stage9C.Material.SpinPair.sourceColorP286Generator g)
    (c.gaugeAuxiliary x pair)
  scalar x:=scalarDirection g (theta x) (c.scalar x)
  matter x:=(theta x:ℂ) • diracExteriorMotherLieAction (nativeMother (colorLie g)) (c.matter x)
  conjugateMatter x:=-(theta x:ℂ) • ((c.conjugateMatter x).comp (diracExteriorMotherLieAction (nativeMother (colorLie g))))

def configurationRay (c d : StageNineHolonomicConfiguration) (r : ℝ) : StageNineHolonomicConfiguration where
  coframe x:=c.coframe x+r • d.coframe x
  gravityConnection x:=c.gravityConnection x+r • d.gravityConnection x
  gravityAuxiliary x:=c.gravityAuxiliary x+r • d.gravityAuxiliary x
  gravitySimplicityMultiplier x:=c.gravitySimplicityMultiplier x+r • d.gravitySimplicityMultiplier x
  gaugeConnection x mu:=c.gaugeConnection x mu+r • d.gaugeConnection x mu
  gaugeAuxiliary x pair:=c.gaugeAuxiliary x pair+r • d.gaugeAuxiliary x pair
  scalar x:=c.scalar x+r • d.scalar x
  matter x:=c.matter x+r • d.matter x
  conjugateMatter x:=c.conjugateMatter x+r • d.conjugateMatter x

def configurationState (c : StageNineHolonomicConfiguration) (x : BasePoint) : ActionState:=
  (c.coframe x,(fun mu=>Quantum.operatorMatrix (FullQuantum.connection c x mu)),scalarLinear (c.scalar x))

 theorem configurationState_emitter (z : SourceCoordinateSlice) : configurationState (emitter z) 0=sourceState z :=rfl

 theorem originalSpin_internal_commute (a : NativeLie) (D : DiracMatrix) :
    nativePrimal a*spinCoordinates D=spinCoordinates D*nativePrimal a :=by
  rw [nativePrimal_mother]
  change Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))*
      Quantum.operatorMatrix (diracMatrixMatterAction D)=
    Quantum.operatorMatrix (diracMatrixMatterAction D)*Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition]
  apply congrArg Quantum.operatorMatrix
  apply LinearMap.ext
  intro v
  simpa only [diracExteriorMotherLieAction,LinearMap.comp_apply] using
    (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal D (exteriorSpinorMotherLieAction (nativeMother a))) v).symm

 theorem originalConnection_source (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu : Fin 4) :
    Quantum.operatorMatrix (FullQuantum.connection c x mu)=
      spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (c.gravityConnection x) mu)+
        nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu)) :=by
  have native : nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu))=
      Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (c.gaugeConnection x mu))):=by
    rw [nativePrimal_mother]
    exact congrArg (fun b=>Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed b)))
      (p286CoordinateEquiv.symm_apply_apply (c.gaugeConnection x mu))
  have original:=Quantum.operatorMatrix.map_add
    (diracMatrixMatterAction (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (c.gravityConnection x) mu))
    (diracExteriorMotherLieAction (p286LieBlockEmbed (c.gaugeConnection x mu)))
  exact original.trans (congrArg (fun M : SourceMatrix=>spinCoordinates
    (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (c.gravityConnection x) mu)+M) native.symm)

 theorem colorPrimitive_state (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    configurationState (colorPrimitiveDirection g theta parameterDerivative c) x=
      stateVariation (Fin.castAdd 6 g) (theta x) (parameterDerivative x) (configurationState c x) :=by
  apply Prod.ext
  · change 0=(theta x • nativeFrameGenerator (Fin.castAdd 6 g))*c.coframe x
    simp [nativeFrameGenerator]
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (colorPrimitiveDirection g theta parameterDerivative c) x mu)=
      theta x • (nativeMatterGenerator (Fin.castAdd 6 g)*Quantum.operatorMatrix (FullQuantum.connection c x mu)-
        Quantum.operatorMatrix (FullQuantum.connection c x mu)*nativeMatterGenerator (Fin.castAdd 6 g))-
          parameterDerivative x mu • nativeMatterGenerator (Fin.castAdd 6 g)
    rw [originalConnection_source,originalConnection_source]
    change spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (p286CoordinateEquiv.symm
        (gaugeDirection g (theta x) (parameterDerivative x)
          (fun nu=>show NativeLie from p286CoordinateEquiv (c.gaugeConnection x nu)) mu)))=
      theta x • (nativeMatterGenerator (Fin.castAdd 6 g)*
          (spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (c.gravityConnection x) mu)+
            nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu)))-
        (spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (c.gravityConnection x) mu)+
          nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu)))*
            nativeMatterGenerator (Fin.castAdd 6 g))-
        parameterDerivative x mu • nativeMatterGenerator (Fin.castAdd 6 g)
    rw [LinearEquiv.apply_symm_apply]
    have spinzero : PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu=0:=
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu).map_zero
    simp only [spinzero,map_zero,zero_add]
    rw [gaugeDirection_source,←colorLie_original,mul_add,add_mul,originalSpin_internal_commute]
    congr 2
    abel
  · exact scalarDirection_source g (theta x) (c.scalar x)

 theorem colorPrimitive_independent_pair (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    (colorPrimitiveDirection g theta parameterDerivative c).conjugateMatter x (c.matter x)+
      c.conjugateMatter x ((colorPrimitiveDirection g theta parameterDerivative c).matter x)=0 :=by
  change (-(theta x:ℂ)) • c.conjugateMatter x
    (diracExteriorMotherLieAction (nativeMother (colorLie g)) (c.matter x))+
      c.conjugateMatter x ((theta x:ℂ) • diracExteriorMotherLieAction (nativeMother (colorLie g)) (c.matter x))=0
  rw [map_smul,neg_smul]
  exact neg_add_cancel _

 theorem colorPrimitive_BF (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c : StageNineHolonomicConfiguration) (x : BasePoint) (pair : Fin 6) :
    (colorPrimitiveDirection g theta parameterDerivative c).gaugeAuxiliary x pair=
      p286LieBracket ((theta x) • Stage9C.Material.SpinPair.sourceColorP286Generator g) (c.gaugeAuxiliary x pair) :=by
  exact (p286LieBracket_smul_left _ _ _).symm

 theorem colorPrimitive_emitted_state (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (z : SourceCoordinateSlice) :
    configurationState (colorPrimitiveDirection g theta parameterDerivative (emitter z)) 0=
      stateVariation (Fin.castAdd 6 g) (theta 0) (parameterDerivative 0) (sourceState z) :=by
  rw [colorPrimitive_state,configurationState_emitter]

 theorem colorPrimitive_current_generated (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (sourceState z.val+
      r • configurationState (colorPrimitiveDirection g theta parameterDerivative (emitter z.val)) 0))
      (nativeFirst (Fin.castAdd 6 g) (theta 0) (parameterDerivative 0) p (sourceState z.val)) 0 :=by
  rw [colorPrimitive_emitted_state]
  exact nativeFirst_generated (Fin.castAdd 6 g) (theta 0) (parameterDerivative 0) p z

 theorem configurationState_ray (c d : StageNineHolonomicConfiguration) (x : BasePoint) (r : ℝ) :
    configurationState (configurationRay c d r) x=configurationState c x+r • configurationState d x :=by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (configurationRay c d r) x mu)=
      Quantum.operatorMatrix (FullQuantum.connection c x mu)+r • Quantum.operatorMatrix (FullQuantum.connection d x mu)
    rw [originalConnection_source,originalConnection_source,originalConnection_source]
    let S:=(spinCoordinates.restrictScalars ℝ).comp (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu)
    change S (c.gravityConnection x+r • d.gravityConnection x)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu+r • d.gaugeConnection x mu))=
        (S (c.gravityConnection x)+nativePrimal (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu)))+
          r • (S (d.gravityConnection x)+nativePrimal (show NativeLie from p286CoordinateEquiv (d.gaugeConnection x mu)))
    rw [map_add,map_smul,p286CoordinateEquiv.map_add,p286CoordinateEquiv.map_smul]
    change _+nativePrimal ((show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu))+
      r • (show NativeLie from p286CoordinateEquiv (d.gaugeConnection x mu)))=_
    rw [map_add,map_smul,smul_add]
    abel
  · change scalarLinear (c.scalar x+r • d.scalar x)=scalarLinear (c.scalar x)+r • scalarLinear (d.scalar x)
    exact (scalarLinear.restrictScalars ℝ).map_add _ _ |>.trans (congrArg (fun v=>scalarLinear (c.scalar x)+v)
      ((scalarLinear.restrictScalars ℝ).map_smul r (d.scalar x)))

 theorem colorPrimitive_stateContact_generated (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c d : StageNineHolonomicConfiguration) (x : BasePoint) :
    HasDerivAt (fun r : ℝ=>configurationState
      (colorPrimitiveDirection g theta parameterDerivative (configurationRay c d r)) x)
      (stateContact (Fin.castAdd 6 g) (theta x) (configurationState d x)) 0 :=by
  have actual:=stateContact_generated (Fin.castAdd 6 g) (theta x) (parameterDerivative x)
    (configurationState c x) (configurationState d x)
  simpa only [colorPrimitive_state,configurationState_ray] using actual

 theorem colorPrimitive_BFContact_generated (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (c d : StageNineHolonomicConfiguration) (x : BasePoint) (pair : Fin 6) :
    HasDerivAt (fun r : ℝ=>show NativeLie from p286CoordinateEquiv
      ((colorPrimitiveDirection g theta parameterDerivative (configurationRay c d r)).gaugeAuxiliary x pair))
      ((theta x) • (show NativeLie from p286CoordinateEquiv (p286LieBracket
        (Stage9C.Material.SpinPair.sourceColorP286Generator g) (d.gaugeAuxiliary x pair)))) 0 :=by
  let base : NativeLie:=p286CoordinateEquiv (p286LieBracket
    (Stage9C.Material.SpinPair.sourceColorP286Generator g) (c.gaugeAuxiliary x pair))
  let contact : NativeLie:=p286CoordinateEquiv (p286LieBracket
    (Stage9C.Material.SpinPair.sourceColorP286Generator g) (d.gaugeAuxiliary x pair))
  have shape (r : ℝ) : (show NativeLie from p286CoordinateEquiv
      ((colorPrimitiveDirection g theta parameterDerivative (configurationRay c d r)).gaugeAuxiliary x pair))=
        (theta x) • base+r • ((theta x) • contact):=by
    change (show NativeLie from p286CoordinateEquiv ((theta x) • p286LieBracket
      (Stage9C.Material.SpinPair.sourceColorP286Generator g) (c.gaugeAuxiliary x pair+r • d.gaugeAuxiliary x pair)))=_
    rw [p286LieBracket_add_right,p286LieBracket_smul_right,p286CoordinateEquiv.map_smul,
      p286CoordinateEquiv.map_add,p286CoordinateEquiv.map_smul]
    change (theta x) • (base+r • contact)=_
    rw [smul_add,smul_comm (theta x) r]
  have actual:=((hasDerivAt_id (0:ℝ)).smul_const ((theta x) • contact)).const_add ((theta x) • base)
  convert! actual using 1
  · exact funext shape
  · simp only [one_smul,contact]

end LowEnergy.PreparationVacuumNativeFieldInjection
