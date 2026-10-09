import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginWardWeight
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeReferenceWard

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen GaussNativeMatter CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumNoetherChart
open SourceQuantumFockGauge GaussQuantumMultiplier
open ActualEMOriginWard
open Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact
open scoped Matrix BigOperators Topology

/-- Three actual action directions, with the scalar and emitted-configuration terms retained separately. -/
inductive PhasePart where
  | ward | scalar | deviation
  deriving DecidableEq, Fintype

def phaseDirection : PhasePart→ActionState→ActionState
  | .ward,s=>emGaugeState s
  | .scalar,_=>emScalarCounterState
  | .deviation,s=>emOriginDeviationState s

def phaseDirectionContact : PhasePart→Field289→ActionState
  | .ward,f=>emGaugeState (fieldDirection f)
  | .scalar,_=>0
  | .deviation,f=>emGaugeState (fieldDirection f)

/-- The density weight is held at the source base; only the original action symbol and direction vary. -/
def phaseHeldAction (part : PhasePart) (p : PhysicalMomentum) (base candidate : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight base*symbolFirst p candidate (phaseDirection part candidate))

def phaseHeldMixed (part : PhasePart) (force : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight base*
    (symbolSecond p candidate (phaseDirection part candidate) (fieldDirection force)+
      symbolFirst p candidate (phaseDirectionContact part force)))

private theorem weighted_three (D : ActionState→L[ℝ]FullMatrix) (W : FullMatrix)
    (c : ℝ) (v a b d : ActionState) (same : v=c • a+b+d) :
    c • (-(4:ℂ) • (W*D a))=
      -(4:ℂ) • (W*D v)-(-(4:ℂ) • (W*D b))-(-(4:ℂ) • (W*D d)) := by
  let L : ActionState→ₗ[ℝ]FullMatrix:=
    -(4:ℂ) • ((LinearMap.mulLeft ℝ W).comp D.toLinearMap)
  have paid:=congrArg L same
  simp only [map_add,map_smul] at paid
  change L v=c • L a+L b+L d at paid
  change c • L a=L v-L b-L d
  rw [paid]
  abel

private theorem weighted_three_contact (D : ActionState→L[ℝ]FullMatrix) (W q : FullMatrix)
    (c : ℝ) (v a b d : ActionState) (same : v=c • a+b+d) :
    c • (-(4:ℂ) • (W*D a))=
      -(4:ℂ) • (W*(D v+q))-(-(4:ℂ) • (W*(D b+0)))-(-(4:ℂ) • (W*(D d+q))) := by
  have paid:=weighted_three D W c v a b d same
  simp only [add_zero,mul_add,smul_add]
  rw [paid]
  abel

theorem phase_held_gradient (p : PhysicalMomentum) (base candidate : ActionState) :
    (gaugeScale/2:ℝ) • sourceFixedMomentumGradient sourceModeField p base candidate=
      phaseHeldAction .ward p base candidate-phaseHeldAction .scalar p base candidate-
        phaseHeldAction .deviation p base candidate :=
  weighted_three (fderiv ℝ (sourceSymbol p) candidate) (sourceActionWeight base)
    (gaugeScale/2) (emGaugeState candidate) (fieldDirection sourceModeField)
    emScalarCounterState (emOriginDeviationState candidate) (em_origin_emitted_state candidate)

theorem phase_held_contact (force : Field289) (p : PhysicalMomentum) (base candidate : ActionState) :
    (gaugeScale/2:ℝ) • sourceFixedMomentumContact sourceModeField force p base candidate=
      phaseHeldMixed .ward force p base candidate-phaseHeldMixed .scalar force p base candidate-
        phaseHeldMixed .deviation force p base candidate := by
  simpa only [phaseHeldMixed,phaseDirection,phaseDirectionContact,symbolFirst,map_zero,add_zero,
    sourceFixedMomentumContact,symbolSecond] using weighted_three_contact
    (fderiv ℝ (fderiv ℝ (sourceSymbol p)) candidate (fieldDirection force))
    (sourceActionWeight base) (symbolFirst p candidate (emGaugeState (fieldDirection force)))
    (gaugeScale/2) (emGaugeState candidate) (fieldDirection sourceModeField)
    emScalarCounterState (emOriginDeviationState candidate) (em_origin_emitted_state candidate)

/-- This is the full independent-dual phase commutator, with the original base weight held. -/
theorem phase_held_ward_generated (p : PhysicalMomentum) (base candidate : ActionState)
    (valid : candidate∈validStates) :
    phaseHeldAction .ward p base candidate=
      -(4:ℂ) • (sourceActionWeight base*emBackgroundFullAd (sourceSymbol p candidate)) := by
  exact congrArg (fun M : FullMatrix=> -(4:ℂ) • (sourceActionWeight base*M))
    (emBackgroundSymbol p candidate valid)

theorem phase_held_mixed_generated (force : Field289) (p : PhysicalMomentum) (base candidate : ActionState)
    (valid : candidate∈validStates) :
    phaseHeldMixed .ward force p base candidate=
      -(4:ℂ) • (sourceActionWeight base*emBackgroundFullAd (symbolFirst p candidate (fieldDirection force))) := by
  exact congrArg (fun M : FullMatrix=> -(4:ℂ) • (sourceActionWeight base*M))
    (emBackgroundMixed_return p candidate valid force)

theorem phase_held_transport (p : PhysicalMomentum) (base candidate : ActionState)
    (valid : candidate∈validStates) :
    (gaugeScale/2:ℝ) • transportedRawSymbol sourceModeField base candidate p=
      phaseHeldAction .ward p base candidate-phaseHeldAction .scalar p base candidate-
        phaseHeldAction .deviation p base candidate := by
  rw [←sourceFixedMomentumGradient_raw sourceModeField p base candidate valid]
  exact phase_held_gradient p base candidate

/-- Every occupation and both independent full504 branches consume the same held-action return. -/
theorem phase_held_quantized (p : PhysicalMomentum) (base candidate : ActionState)
    (valid : candidate∈validStates) :
    (gaugeScale/2:ℝ) • quantizer (transportedRawSymbol sourceModeField base candidate p)=
      quantizer (phaseHeldAction .ward p base candidate)-quantizer (phaseHeldAction .scalar p base candidate)-
        quantizer (phaseHeldAction .deviation p base candidate) := by
  have paid:=congrArg quantizer (phase_held_transport p base candidate valid)
  simpa only [map_sub,LinearMap.map_smul_of_tower] using paid

end LowEnergy.GaussComposite.ActualDressedPhaseWard
