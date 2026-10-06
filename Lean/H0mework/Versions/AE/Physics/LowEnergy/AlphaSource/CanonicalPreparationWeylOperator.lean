import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylTemperedAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOperator
open PreparationVacuumWeyl PreparationVacuumWeylDomain CanonicalPreparationSquareCutoff
open GaussDensityCore SourceQuantumGaugeSliceCoordinates MeasureTheory Filter
open scoped SchwartzMap FourierTransform

def dividedActionLpLinear :
    𝓢(PhysicalMomentum,ℂ) →ₗ[ℂ] Lp (α := PhysicalMomentum) ℂ ⊤ volume where
  toFun := dividedActionLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(dividedAction_memLp (f+g)).coeFn_toLp,
      (dividedAction_memLp f).coeFn_toLp,(dividedAction_memLp g).coeFn_toLp,
      Lp.coeFn_add (dividedActionLp f) (dividedActionLp g)] with xi hsum hf hg hout
    change dividedActionLp (f+g) xi=(dividedActionLp f+dividedActionLp g) xi
    change ((dividedAction_memLp (f+g)).toLp (dividedAction (f+g))) xi=
      (dividedActionLp f+dividedActionLp g) xi
    rw [hsum,hout]
    change dividedAction (f+g) xi=((dividedAction_memLp f).toLp (dividedAction f)) xi+
      ((dividedAction_memLp g).toLp (dividedAction g)) xi
    rw [hf,hg]
    simp only [dividedAction,fourierAction_add,Pi.add_apply,add_div]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(dividedAction_memLp (c • f)).coeFn_toLp,(dividedAction_memLp f).coeFn_toLp,
      Lp.coeFn_smul c (dividedActionLp f)] with xi hc hf hout
    change dividedActionLp (c • f) xi=(c • dividedActionLp f) xi
    rw [hout]
    change ((dividedAction_memLp (c • f)).toLp (dividedAction (c • f))) xi=
      c • ((dividedAction_memLp f).toLp (dividedAction f)) xi
    rw [hc,hf]
    simp only [dividedAction,fourierAction_smul,Pi.smul_apply,smul_eq_mul]
    ring

def temperedActionLinear : 𝓢(PhysicalMomentum,ℂ) →ₗ[ℂ] 𝓢'(PhysicalMomentum,ℂ) :=
  (TemperedDistribution.smulLeftCLM ℂ polynomialWeight).toLinearMap.comp
    ((Lp.toTemperedDistributionCLM ℂ volume ⊤).toLinearMap.comp dividedActionLpLinear)

theorem temperedActionLinear_apply (f : 𝓢(PhysicalMomentum,ℂ)) :
    temperedActionLinear f=temperedAction f := rfl

def sourcePositionProfileLinear (N : ℕ) : ScalarTest →ₗ[ℂ] 𝓢(PhysicalMomentum,ℂ) where
  toFun := sourcePositionProfile N
  map_add' f g := by
    apply SchwartzMap.ext
    intro xi
    simp only [sourcePositionProfile_apply,map_add,add_apply]
  map_smul' c f := by
    apply SchwartzMap.ext
    intro xi
    simp only [sourcePositionProfile_apply,map_smul,smul_apply,RingHom.id_apply]

def sourceVacuumFrequencyLinear : ScalarTest →ₗ[ℂ] 𝓢(PhysicalMomentum,ℂ) :=
  (FourierTransform.fourierCLM ℂ 𝓢(PhysicalMomentum,ℂ)).toLinearMap.comp
    ((sourcePositionProfileLinear 0).comp sourceVacuumInputCore)

theorem sourceVacuumFrequencyLinear_apply (f : ScalarTest) :
    sourceVacuumFrequencyLinear f=sourceVacuumInputFrequency f := rfl

def actualVacuumTemperedLinear : ScalarTest →ₗ[ℂ] 𝓢'(PhysicalMomentum,ℂ) :=
  temperedActionLinear.comp sourceVacuumFrequencyLinear

theorem actualVacuumTemperedLinear_apply (f : ScalarTest) :
    actualVacuumTemperedLinear f=actualVacuumTemperedAction f := rfl

def actualVacuumWeyl : ScalarTest →ₗ[ℂ] 𝓢'(PhysicalMomentum,ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢'(PhysicalMomentum,ℂ)).toLinearMap.comp
    actualVacuumTemperedLinear

theorem actualVacuumWeyl_readback (f : ScalarTest) (g : 𝓢(PhysicalMomentum,ℂ)) :
    actualVacuumWeyl f g=
      ∫ xi : PhysicalMomentum,(𝓕⁻ g) xi*actualVacuumFactorAction f xi := by
  change (𝓕⁻ (actualVacuumTemperedAction f)) g= _
  rw [TemperedDistribution.fourierInv_apply]
  exact actualVacuumTemperedAction_readback _ _

end LowEnergy.PreparationVacuumWeylOperator
