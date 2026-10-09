import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPrimitiveColorFields
import H0mework.Physics.GaugeAction.P286InfinitesimalGaugeTransformation
import H0mework.Physics.GaugeStanding.GaugeBFAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation StageNineP286BracketCalculus
open StageNineP286InfinitesimalGaugeTransformation StageNineP286LinkedActiveGaugeBFAlgebra SourceQuantumScalarChart
open StageNineCompactSupportIntegrationByParts GaussHistoryHilbert
open PreparationVacuumNativeLocalWard PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open Filter Set
open scoped Topology ContDiff BigOperators
local instance : Fintype P286CoordinateIndex:=StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype

def lie (a b : NativeLie) : NativeLie:=coordinateBracket a b

 theorem lie_derivation (a b c : NativeLie) : lie a (lie b c)=lie (lie a b) c+lie b (lie a c) :=
  coordinateBracket_derivation_left a b c

 def curvature (A : Fin 4→NativeLie) (dA : Fin 4→Fin 4→NativeLie) (pair : Fin 6) : NativeLie:=
  dA (pairFirst pair) (pairSecond pair)-dA (pairSecond pair) (pairFirst pair)+
    lie (A (pairFirst pair)) (A (pairSecond pair))

 def curvatureFirst (A f : Fin 4→NativeLie) (df : Fin 4→Fin 4→NativeLie) (pair : Fin 6) : NativeLie:=
  df (pairFirst pair) (pairSecond pair)-df (pairSecond pair) (pairFirst pair)+
    lie (f (pairFirst pair)) (A (pairSecond pair))+lie (A (pairFirst pair)) (f (pairSecond pair))

 def curvatureSecond (f h : Fin 4→NativeLie) (pair : Fin 6) : NativeLie:=
  lie (f (pairFirst pair)) (h (pairSecond pair))+lie (h (pairFirst pair)) (f (pairSecond pair))

 def nativeGaugeDirection (epsilon : NativeLie) (gradient : Fin 4→NativeLie) (A : Fin 4→NativeLie) : Fin 4→NativeLie:=
  fun mu=>lie epsilon (A mu)-gradient mu

 def nativeGaugeContact (epsilon : NativeLie) (f : Fin 4→NativeLie) : Fin 4→NativeLie:=fun mu=>lie epsilon (f mu)

 def nativeGaugeContactDerivative (epsilon : NativeLie) (gradient f : Fin 4→NativeLie)
    (df : Fin 4→Fin 4→NativeLie) : Fin 4→Fin 4→NativeLie:=
  fun mu nu=>lie (gradient mu) (f nu)+lie epsilon (df mu nu)

/-- Both source curvature legs are retained before their Jacobi combination. -/
 theorem nativeCurvature_mixed (epsilon : NativeLie) (gradient A f : Fin 4→NativeLie)
    (df : Fin 4→Fin 4→NativeLie) (pair : Fin 6) :
    curvatureSecond f (nativeGaugeDirection epsilon gradient A) pair+
      curvatureFirst A (nativeGaugeContact epsilon f) (nativeGaugeContactDerivative epsilon gradient f df) pair=
        lie epsilon (curvatureFirst A f df pair) :=by
  change P286CoordinateCarrier at epsilon
  change Fin 4→P286CoordinateCarrier at gradient A f
  change Fin 4→Fin 4→P286CoordinateCarrier at df
  change (coordinateBracket (f (pairFirst pair))
      (coordinateBracket epsilon (A (pairSecond pair))-gradient (pairSecond pair))+
    coordinateBracket (coordinateBracket epsilon (A (pairFirst pair))-gradient (pairFirst pair))
      (f (pairSecond pair)))+
    (((coordinateBracket (gradient (pairFirst pair)) (f (pairSecond pair))+
      coordinateBracket epsilon (df (pairFirst pair) (pairSecond pair)))-
      (coordinateBracket (gradient (pairSecond pair)) (f (pairFirst pair))+
        coordinateBracket epsilon (df (pairSecond pair) (pairFirst pair))))+
      coordinateBracket (coordinateBracket epsilon (f (pairFirst pair))) (A (pairSecond pair))+
        coordinateBracket (A (pairFirst pair)) (coordinateBracket epsilon (f (pairSecond pair))))=
    coordinateBracket epsilon
      (df (pairFirst pair) (pairSecond pair)-df (pairSecond pair) (pairFirst pair)+
        coordinateBracket (f (pairFirst pair)) (A (pairSecond pair))+
          coordinateBracket (A (pairFirst pair)) (f (pairSecond pair)))
  simp only [coordinateBracket_sub_right,coordinateBracket_sub_left,
    coordinateBracket_add_right,coordinateBracket_add_left]
  conv_rhs=>
    rw [coordinateBracket_derivation_left epsilon (f (pairFirst pair)) (A (pairSecond pair)),
      coordinateBracket_derivation_left epsilon (A (pairFirst pair)) (f (pairSecond pair))]
  rw [coordinateBracket_skew (f (pairFirst pair)) (gradient (pairSecond pair))]
  abel

 def actualConnection (c : StageNineHolonomicConfiguration) (x : BasePoint) : Fin 4→NativeLie:=
  fun mu=>holonomicP286GaugeConnectionCoordinate c x mu

 def actualConnectionDerivative (c : StageNineHolonomicConfiguration) (x : BasePoint) : Fin 4→Fin 4→NativeLie:=
  fun mu nu=>p286GaugeConnectionCoordinateDerivative c x mu nu

 def actualForce (f : BasePoint→P286GaugeOneForm) (x : BasePoint) : Fin 4→NativeLie:=fun mu=>f x mu

 def actualForceDerivative (f : BasePoint→P286GaugeOneForm) (x : BasePoint) : Fin 4→Fin 4→NativeLie:=
  fun mu nu=>p286GaugeVariationCoordinateDerivative f x mu nu

 theorem curvature_original (c : StageNineHolonomicConfiguration) (x : BasePoint) (pair : Fin 6) :
    curvature (actualConnection c x) (actualConnectionDerivative c x) pair=
      (show NativeLie from holonomicP286GaugeCurvatureCoordinate c x pair) :=by
  exact (holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket c x pair).symm

 theorem curvatureFirst_original (c : StageNineHolonomicConfiguration) (f : BasePoint→P286GaugeOneForm)
    (x : BasePoint) (pair : Fin 6) :
    curvatureFirst (actualConnection c x) (actualForce f x) (actualForceDerivative f x) pair=
      (show NativeLie from p286GaugeConnectionLinearCurvatureVariation c f x pair) :=rfl

 theorem actualNativeGaugeDirection (c : StageNineHolonomicConfiguration) (epsilon : P286InfinitesimalGaugeParameter)
    (x : BasePoint) :
    nativeGaugeDirection (show NativeLie from epsilon x)
      (fun mu=>show NativeLie from p286GaugeParameterDerivative epsilon x mu) (actualConnection c x)=
      (fun mu=>show NativeLie from p286InfinitesimalGaugeConnectionDirection c epsilon x mu) :=rfl

 theorem actualNativeCurvature_mixed (c : StageNineHolonomicConfiguration) (epsilon : P286InfinitesimalGaugeParameter)
    (f : BasePoint→P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureSecond (actualForce f x)
        (fun mu=>show NativeLie from p286InfinitesimalGaugeConnectionDirection c epsilon x mu) pair+
      curvatureFirst (actualConnection c x)
        (nativeGaugeContact (show NativeLie from epsilon x) (actualForce f x))
        (nativeGaugeContactDerivative (show NativeLie from epsilon x)
          (fun mu=>show NativeLie from p286GaugeParameterDerivative epsilon x mu)
          (actualForce f x) (actualForceDerivative f x)) pair=
      (show NativeLie from coordinateBracket (epsilon x) (p286GaugeConnectionLinearCurvatureVariation c f x pair)) :=by
  rw [←actualNativeGaugeDirection]
  have generated:=nativeCurvature_mixed (show NativeLie from epsilon x)
    (fun mu=>show NativeLie from p286GaugeParameterDerivative epsilon x mu)
    (actualConnection c x) (actualForce f x) (actualForceDerivative f x) pair
  exact generated.trans (congrArg (lie (show NativeLie from epsilon x)) (curvatureFirst_original c f x pair))

 theorem curvatureSecond_source (f h : BasePoint→P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureSecond (actualForce f x) (actualForce h x) pair=
      (show NativeLie from p286GaugeConnectionQuadraticCurvatureVariation (f+h) x pair-
        p286GaugeConnectionQuadraticCurvatureVariation f x pair-
          p286GaugeConnectionQuadraticCurvatureVariation h x pair) :=by
  unfold curvatureSecond actualForce p286GaugeConnectionQuadraticCurvatureVariation
  simp only [Pi.add_apply,p286CoordinateLieBracket_add_left,p286CoordinateLieBracket_add_right]
  unfold lie coordinateBracket p286CoordinateLieBracket
  abel

def actualNativeContactField (epsilon : P286InfinitesimalGaugeParameter) (f : BasePoint→P286GaugeOneForm) :
    BasePoint→P286GaugeOneForm:=fun x mu=>coordinateBracket (epsilon x) (f x mu)

 theorem actualNativeContact_firstjet (epsilon : P286InfinitesimalGaugeParameter)
    (f : CompactlySupportedSmoothVariation P286GaugeOneForm) (x : BasePoint) (mu nu : Fin 4) :
    p286GaugeVariationCoordinateDerivative (actualNativeContactField epsilon f) x mu nu=
      coordinateBracket (p286GaugeParameterDerivative epsilon x mu) (f x nu)+
        coordinateBracket (epsilon x) (p286GaugeVariationCoordinateDerivative f x mu nu) :=by
  have each : ContDiff ℝ ∞ (fun y=>f y nu):=(contDiff_pi.mp f.smooth) nu
  exact fieldDirectionalDerivative_coordinateBracket epsilon (fun y=>f y nu) epsilon.smooth each x mu

 theorem actualNativeContact_curvatureLeg (c : StageNineHolonomicConfiguration) (epsilon : P286InfinitesimalGaugeParameter)
    (f : CompactlySupportedSmoothVariation P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureFirst (actualConnection c x)
      (nativeGaugeContact (show NativeLie from epsilon x) (actualForce f x))
      (nativeGaugeContactDerivative (show NativeLie from epsilon x)
        (fun mu=>show NativeLie from p286GaugeParameterDerivative epsilon x mu)
        (actualForce f x) (actualForceDerivative f x)) pair=
      (show NativeLie from p286GaugeConnectionLinearCurvatureVariation c (actualNativeContactField epsilon f) x pair) :=by
  unfold curvatureFirst p286GaugeConnectionLinearCurvatureVariation
  rw [actualNativeContact_firstjet,actualNativeContact_firstjet]
  rfl

 theorem actualTwoCurvatureLegs (c : StageNineHolonomicConfiguration) (epsilon : P286InfinitesimalGaugeParameter)
    (f : CompactlySupportedSmoothVariation P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureSecond (actualForce f x)
        (fun mu=>show NativeLie from p286InfinitesimalGaugeConnectionDirection c epsilon x mu) pair+
      (show NativeLie from p286GaugeConnectionLinearCurvatureVariation c (actualNativeContactField epsilon f) x pair)=
      (show NativeLie from coordinateBracket (epsilon x) (p286GaugeConnectionLinearCurvatureVariation c f x pair)) :=by
  rw [←actualNativeContact_curvatureLeg]
  exact actualNativeCurvature_mixed c epsilon f x pair

 theorem actualBF_mixedPair (c : StageNineHolonomicConfiguration) (epsilon : P286InfinitesimalGaugeParameter)
    (f : CompactlySupportedSmoothVariation P286GaugeOneForm) (x : BasePoint) (auxPair pair : Fin 6) :
    p286CoordinateLiePairing (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair))
      (curvatureSecond (actualForce f x)
          (fun mu=>show NativeLie from p286InfinitesimalGaugeConnectionDirection c epsilon x mu) pair+
        (show NativeLie from p286GaugeConnectionLinearCurvatureVariation c (actualNativeContactField epsilon f) x pair))+
    p286CoordinateLiePairing (coordinateBracket (epsilon x) (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair)))
      (p286GaugeConnectionLinearCurvatureVariation c f x pair)=0 :=by
  rw [actualTwoCurvatureLegs]
  have original:=p286CoordinateLiePairing_adjoint_skew (epsilon x)
    (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair)) (p286GaugeConnectionLinearCurvatureVariation c f x pair)
  change _+_=0 at original
  simpa only [p286CoordinateLieBracket_eq_coordinateBracket,add_comm] using original

 theorem actualColorBF_mixedPair (c : StageNineHolonomicConfiguration)
    (g : Fin 3) (theta : BasePoint→ℝ) (parameterDerivative : BasePoint→Fin 4→ℝ)
    (f : BasePoint→P286GaugeOneForm) (x : BasePoint) (auxPair pair : Fin 6) :
    p286CoordinateLiePairing (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair))
      (lie ((theta x) • colorLie g) (curvatureFirst (actualConnection c x) (actualForce f x) (actualForceDerivative f x) pair))+
    p286CoordinateLiePairing
      (p286CoordinateEquiv ((colorPrimitiveDirection g theta parameterDerivative c).gaugeAuxiliary x auxPair))
      (p286GaugeConnectionLinearCurvatureVariation c f x pair)=0 :=by
  rw [colorPrimitive_BF,curvatureFirst_original]
  have identity : p286CoordinateEquiv (p286LieBracket ((theta x) • Stage9C.Material.SpinPair.sourceColorP286Generator g)
      (c.gaugeAuxiliary x auxPair))=
    coordinateBracket ((theta x) • colorLie g) (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair)):=by
    unfold coordinateBracket colorLie
    rw [←p286CoordinateEquiv.map_smul,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  rw [identity]
  have original:=p286CoordinateLiePairing_adjoint_skew ((theta x) • colorLie g)
    (p286CoordinateEquiv (c.gaugeAuxiliary x auxPair)) (p286GaugeConnectionLinearCurvatureVariation c f x pair)
  simpa only [lie,p286CoordinateLieBracket_eq_coordinateBracket,add_comm] using original

 theorem actualColor_preparedSource (g : Fin 3) (theta : BasePoint→ℝ)
    (parameterDerivative : BasePoint→Fin 4→ℝ) (z : physicalChart)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    PreparationVacuumActionFieldLift.symbolFirst p (sourceState z.val)
      (configurationState (colorPrimitiveDirection g theta parameterDerivative (emitter z.val)) 0)=
        nativeFirst (Fin.castAdd 6 g) (theta 0) (parameterDerivative 0) p (sourceState z.val) :=by
  rw [colorPrimitive_emitted_state]
  rfl

end LowEnergy.PreparationVacuumNativeFieldInjection
