import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeSourceInjection
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationTransportedGraded

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumActionFieldLift
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineLorentzConnectionVariation StageNineP286GaugeConnectionVariationDensity
open GaussLiveMomentum GaussMomentumAdjoint
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeMatter
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumGaugeSourceInjection PreparationVacuumSourceActionJets
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The differential of the original emitted ActionState along its configuration slice. -/
def sliceState : SourceCoordinateSlice →ₗ[ℝ] ActionState where
  toFun h:=(GaussNativeEnergy.coframe 0 h.1,
    (fun mu=>Fin.cases 0 (fun j=>nativePrimal (SourceCartanCubic.gaugeCoordinate j (h.2.2:Gauge))) mu),
    scalarLinear (h.2.1:Scalar))
  map_add' h k:=by
    apply Prod.ext
    · ext i j;fin_cases i <;> fin_cases j <;> simp [GaussNativeEnergy.coframe]
    apply Prod.ext
    · funext mu;refine Fin.cases ?_ (fun j=>?_) mu
      · change (0:SourceMatrix)=0+0;exact (zero_add _).symm
      · change nativePrimal (SourceCartanCubic.gaugeCoordinate j ((h.2.2:Gauge)+(k.2.2:Gauge)))=_
        rw [map_add,map_add];rfl
    · exact (scalarLinear.restrictScalars ℝ).map_add _ _
  map_smul' r h:=by
    apply Prod.ext
    · ext i j;fin_cases i <;> fin_cases j <;> simp [GaussNativeEnergy.coframe]
    apply Prod.ext
    · funext mu;refine Fin.cases ?_ (fun j=>?_) mu
      · change (0:SourceMatrix)=r • 0;exact (smul_zero r).symm
      · change nativePrimal (SourceCartanCubic.gaugeCoordinate j (r • (h.2.2:Gauge)))=_
        rw [map_smul,map_smul];rfl
    · exact (scalarLinear.restrictScalars ℝ).map_smul r _

theorem coframe_slice_affine (z h : SourceCoordinateSlice) (r : ℝ) :
    CanonicalGradedSpatialSource.sourceCoframe (z+r • h)=
      CanonicalGradedSpatialSource.sourceCoframe z+r • GaussNativeEnergy.coframe 0 h.1 :=by
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [CanonicalGradedSpatialSource.sourceCoframe,GaussNativeEnergy.coframe]

theorem connection_slice_affine (z h : SourceCoordinateSlice) (r : ℝ) (mu : Fin 4) :
    familyConnection (z+r • h) mu=familyConnection z mu+r • (sliceState h).2.1 mu :=by
  refine Fin.cases ?_ (fun j=>?_) mu
  · change familyConnection z 0=familyConnection z 0+r • 0
    rw [smul_zero,add_zero]
  · rw [connection_spatial,connection_spatial]
    change spinConnection j.succ+nativePrimal (SourceCartanCubic.gaugeCoordinate j ((z.2.2:Gauge)+r • (h.2.2:Gauge)))=
      (spinConnection j.succ+nativePrimal (SourceCartanCubic.gaugeCoordinate j (z.2.2:Gauge)))+
        r • nativePrimal (SourceCartanCubic.gaugeCoordinate j (h.2.2:Gauge))
    simp only [Prod.snd_add,Prod.snd_smul,Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
    exact (add_assoc (spinConnection j.succ) (nativePrimal (SourceCartanCubic.gaugeCoordinate j (z.2.2:Gauge)))
      (r • nativePrimal (SourceCartanCubic.gaugeCoordinate j (h.2.2:Gauge)))).symm

theorem scalar_slice_affine (z h : SourceCoordinateSlice) (r : ℝ) :
    familyScalar (z+r • h)=familyScalar z+r • (sliceState h).2.2 :=by
  change scalarLinear (vacuum+((z+r • h).2.1:Scalar))=
    scalarLinear (vacuum+(z.2.1:Scalar))+r • scalarLinear (h.2.1:Scalar)
  change scalarLinear (vacuum+((z.2.1:Scalar)+r • (h.2.1:Scalar)))=_
  rw [←add_assoc,map_add]
  exact congrArg (fun M : SourceMatrix=>scalarLinear (vacuum+(z.2.1:Scalar))+M)
    ((scalarLinear.restrictScalars ℝ).map_smul r (h.2.1:Scalar))

theorem sourceState_affine (z h : SourceCoordinateSlice) (r : ℝ) :
    sourceState (z+r • h)=sourceState z+r • sliceState h :=by
  apply Prod.ext
  · exact coframe_slice_affine z h r
  apply Prod.ext
  · exact funext (connection_slice_affine z h r)
  · exact scalar_slice_affine z h r

def sliceStateCLM : SourceCoordinateSlice →L[ℝ] ActionState:=sliceState.toContinuousLinearMap

theorem sourceState_fderiv (z : SourceCoordinateSlice) : fderiv ℝ sourceState z=sliceStateCLM :=by
  have identity : sourceState=fun x=>sourceState 0+sliceStateCLM x :=by
    funext x
    change sourceState x=sourceState 0+sliceState x
    simpa only [one_smul,zero_add] using sourceState_affine 0 x 1
  rw [identity]
  exact (sliceStateCLM.hasFDerivAt.const_add (sourceState 0)).fderiv

def complement (f : Field289) (z : SourceCoordinateSlice) : ActionState :=
  fieldDirection f-sliceState (fieldVector f z)

def stateSquare (f : Field289) (z : SourceCoordinateSlice) (r s : ℝ) : ActionState :=
  sourceState (fieldCoordinateCurve f r z)+s • complement f z

theorem stateSquare_coordinate (f : Field289) (z : SourceCoordinateSlice) (r : ℝ) :
    stateSquare f z r 0=sourceState (fieldCoordinateCurve f r z) :=by
  rw [stateSquare,zero_smul,add_zero]

theorem stateSquare_ambient (f : Field289) (z : SourceCoordinateSlice) (r : ℝ) :
    stateSquare f z r r=sourceState z+r • fieldDirection f :=by
  rw [stateSquare,fieldCoordinateCurve,sourceState_affine,complement]
  module

theorem complement_smooth (f : Field289) (z : physicalChart) : ContDiffAt ℝ ∞ (complement f) z.val :=
  contDiffAt_const.sub (sliceStateCLM.contDiff.contDiffAt.comp z.val (fieldVector_smooth f z))

theorem stateSquare_smooth (f : Field289) (r s : ℝ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun u : (ℝ×ℝ)×SourceCoordinateSlice=>stateSquare f u.2 u.1.1 u.1.2) ((r,s),z.val) :=by
  have point : ContDiffAt ℝ ∞ (fun u : (ℝ×ℝ)×SourceCoordinateSlice=>fieldCoordinateCurve f u.1.1 u.2) ((r,s),z.val) :=
    (field_curve_smooth f r z).comp ((r,s),z.val) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have h : ContDiffAt ℝ ∞ (fun u : (ℝ×ℝ)×SourceCoordinateSlice=>complement f u.2) ((r,s),z.val) :=by
    have hs : ContDiffAt ℝ ∞ (Prod.snd : (ℝ×ℝ)×SourceCoordinateSlice→SourceCoordinateSlice) ((r,s),z.val) :=contDiffAt_snd
    have hh:=(complement_smooth f z).comp ((r,s),z.val) hs
    exact hh
  have scalar : ContDiffAt ℝ ∞ (fun u : (ℝ×ℝ)×SourceCoordinateSlice=>u.1.2) ((r,s),z.val) :=contDiffAt_fst.snd
  exact (sourceState_smooth.contDiffAt.comp ((r,s),z.val) point).add (scalar.smul h)

lemma coframe_split (time : Fin 4→ℝ) (h : Coframe) :
    GaussNativeEnergy.coframe time h-GaussNativeEnergy.coframe 0 h=GaussNativeEnergy.coframe time 0 :=by
  ext i j;fin_cases i <;> fin_cases j <;> simp [GaussNativeEnergy.coframe]

theorem complement_coframe (f : Field289) (z : physicalChart) :
    (complement f z.val).1=GaussNativeEnergy.coframe (remainingChannels f z.val).time 0+
      (remainingChannels f z.val).frame*CanonicalGradedSpatialSource.sourceCoframe z.val :=by
  change fieldCoframe f-GaussNativeEnergy.coframe 0 (coframeSliceDirection f z.val)=_
  rw [coframe_field_reconstruction f z]
  have split:=coframe_split (coframeTimeDirection f z.val) (coframeSliceDirection f z.val)
  change GaussNativeEnergy.coframe (coframeTimeDirection f z.val) (coframeSliceDirection f z.val)+
    lorentzPart (normalizedCoframe f z.val)*CanonicalGradedSpatialSource.sourceCoframe z.val-
    GaussNativeEnergy.coframe 0 (coframeSliceDirection f z.val)=_
  calc
    _=(GaussNativeEnergy.coframe (coframeTimeDirection f z.val) (coframeSliceDirection f z.val)-
      GaussNativeEnergy.coframe 0 (coframeSliceDirection f z.val))+
      lorentzPart (normalizedCoframe f z.val)*CanonicalGradedSpatialSource.sourceCoframe z.val :=by abel
    _=_ :=congrArg (fun A : LorentzianCoframe=>A+lorentzPart (normalizedCoframe f z.val)*CanonicalGradedSpatialSource.sourceCoframe z.val) split

theorem complement_scalar (f : Field289) (z : physicalChart) :
    (complement f z.val).2.2=scalarLinear (scalarP286ActionBilinear
      (remainingChannels f z.val).gaugeOrbit (scalarField z.val)) :=by
  rw [complement,←stateDirection_source f]
  change scalarLinear (fieldScalar f)-scalarLinear ((gaugeParameters f z.val).2.1:Scalar)=_
  rw [←map_sub]
  have original:=scalar_tangent_reconstruction f z
  have eq : fieldScalar f-((gaugeParameters f z.val).2.1:Scalar)=
      scalarP286ActionBilinear (gaugeOrbitParameter f z.val) (scalarField z.val) :=by rw [←original];abel
  rw [eq]
  rfl

theorem complement_temporal (f : Field289) (z : SourceCoordinateSlice) :
    (complement f z).2.1 0=spinLinear 0 (remainingChannels f z).lorentz+
      nativePrimal (remainingChannels f z).temporalGauge :=by
  rw [complement,←stateDirection_source f]
  change spinLinear 0 (fieldLorentz f)+nativePrimal (fieldGauge f 0)-0=_
  rw [sub_zero]
  rfl

theorem complement_spatial (f : Field289) (z : physicalChart) (i : Fin 3) :
    (complement f z.val).2.1 i.succ=spinLinear i.succ (remainingChannels f z.val).lorentz+
      nativePrimal (SourceCartanCubic.gaugeCoordinate i (nativeGauge (remainingChannels f z.val).gaugeOrbit (z.val.2.2:Gauge))) :=by
  rw [complement,←stateDirection_source f]
  change (spinLinear i.succ (fieldLorentz f)+nativePrimal (fieldGauge f i.succ))-
    nativePrimal (SourceCartanCubic.gaugeCoordinate i ((gaugeParameters f z.val).2.2:Gauge))=_
  rw [←spatial_gauge_tangent_reconstruction f z i,map_add]
  abel

def fieldDirectionLinear : Field289 →ₗ[ℝ] ActionState where
  toFun:=fieldDirection
  map_add' f g:=by
    have source : sourceData (f+g)=sourceData f+sourceData g :=by
      apply Prod.ext
      · exact fieldScalar_add f g
      apply Prod.ext
      · exact funext (fieldGauge_add f g)
      apply Prod.ext <;> rfl
    rw [←stateDirection_source,source,map_add,stateDirection_source,stateDirection_source]
  map_smul' r f:=by
    have source : sourceData (r • f)=r • sourceData f :=by
      apply Prod.ext
      · exact fieldScalar_smul r f
      apply Prod.ext
      · exact funext (fieldGauge_smul r f)
      apply Prod.ext <;> rfl
    rw [←stateDirection_source,source,map_smul,stateDirection_source]
    rfl

def fieldUnit (i : Fin 289) : Field289:=Pi.single i 1

theorem fieldDirection_coordinates (f : Field289) :
    fieldDirection f=∑i : Fin 289,f i • fieldDirection (fieldUnit i) :=by
  have coordinates : f=∑i : Fin 289,f i • fieldUnit i :=by
    funext j
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply,ite_smul]
  have read:=congrArg fieldDirectionLinear coordinates
  simp only [map_sum,map_smul] at read
  exact read

end LowEnergy.PreparationVacuumActionFieldLift
