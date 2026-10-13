import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Profiles
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "S" => burnolMeanZeroTruncatedFourier

theorem evenBandDerivative_continuous (h scale : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) : Continuous (evenBandDerivative h scale raw) := by
  have derivative:=bandDerivative_continuous h raw continuous
  unfold evenBandDerivative
  fun_prop

theorem actual_derivatives_continuous (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    Continuous (xDerivative coordinate h).1 ∧ Continuous (yDerivative coordinate h).1 ∧
    Continuous (xDerivative coordinate h).2 ∧ Continuous (yDerivative coordinate h).2 :=
  ⟨(evenBandDerivative_continuous h (-h/2) (bLeg coordinate (h/2))
      (bLeg_continuousOn coordinate h (h/2))).add (state_derivative_continuous _),
    (state_derivative_continuous _).sub
      (evenBandDerivative_continuous h (-h/2) (pLeg coordinate (h/2))
        (pLeg_continuousOn coordinate h (h/2))),
    (evenBandDerivative_continuous h (h/2) (bLeg coordinate (-h/2))
      (bLeg_continuousOn coordinate h (-h/2))).add (state_derivative_continuous _),
    (state_derivative_continuous _).sub
      (evenBandDerivative_continuous h (h/2) (pLeg coordinate (-h/2))
        (pLeg_continuousOn coordinate h (-h/2)))⟩

def eulerRaw (raw derivative : ℝ→ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)*derivative x+(1/2:ℂ)*raw x
theorem eulerRaw_continuous (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative) :
    Continuous (eulerRaw raw derivative) := by
  unfold eulerRaw
  fun_prop

def eulerAmbient (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative) :
    BurnolQuarterIntervalL2 :=
  Constructor.compact (eulerRaw raw derivative)
    (eulerRaw_continuous raw derivative rawContinuous derivativeContinuous)
def eulerState (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative) :
    BurnolQuarterMeanZeroCarrier := Constructor.zeroMean
      (eulerAmbient raw derivative rawContinuous derivativeContinuous)

theorem raw_fourier_ward (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (actualDerivative : ∀ x:ℝ,HasDerivAt raw (derivative x) x) (frequency : ℝ) :
    (frequency:ℂ)*Constructor.fourierDerivative raw frequency+
      (1/2:ℂ)*Constructor.fourierRaw raw frequency+
      Constructor.fourierRaw (eulerRaw raw derivative) frequency=
      (q:ℂ)*(Constructor.phase frequency q*raw q+
        Constructor.phase frequency (-q)*raw (-q)) := by
  let primitive:=fun x:ℝ=>(x:ℂ)*Constructor.phase frequency x*raw x
  let density:=fun x:ℝ=>Constructor.phase frequency x*
    ((1-2*(Real.pi:ℂ)*Complex.I*(frequency:ℂ)*(x:ℂ))*raw x+(x:ℂ)*derivative x)
  have generated (x : ℝ) : HasDerivAt primitive (density x) x := by
    have source:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul
      (Constructor.phase_derivative frequency x)).mul (actualDerivative x)
    convert! source using 1
    dsimp only [density,Complex.ofRealCLM_apply,Pi.mul_apply,Complex.ofReal_one]
    ring
  have densityContinuous : Continuous density := by
    have phase:=Constructor.phaseContinuous frequency
    dsimp only [density]
    fun_prop
  have integral:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _=>generated x) (densityContinuous.intervalIntegrable (-q) q)
  rw [Constructor.fourierDerivative_integral raw rawContinuous,
    Constructor.fourierRaw_integral,Constructor.fourierRaw_integral]
  let moment:=fun x:ℝ=>Constructor.phase frequency x*
    (-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*raw x)
  let returned:=fun x:ℝ=>Constructor.phase frequency x*raw x
  let euler:=fun x:ℝ=>Constructor.phase frequency x*eulerRaw raw derivative x
  have momentContinuous : Continuous moment := by
    have phase:=Constructor.phaseContinuous frequency
    dsimp only [moment]
    fun_prop
  have returnedContinuous : Continuous returned := (Constructor.phaseContinuous frequency).mul rawContinuous
  have eulerContinuous : Continuous euler := (Constructor.phaseContinuous frequency).mul
    (eulerRaw_continuous raw derivative rawContinuous derivativeContinuous)
  change (frequency:ℂ)*(∫ x:ℝ in (-q)..q,moment x)+
    (1/2:ℂ)*(∫ x:ℝ in (-q)..q,returned x)+(∫ x:ℝ in (-q)..q,euler x)=_
  calc
    _=∫ x:ℝ in (-q)..q,((frequency:ℂ)*moment x+(1/2:ℂ)*returned x)+euler x := by
      rw [intervalIntegral.integral_add
        (f:=fun x=>(frequency:ℂ)*moment x+(1/2:ℂ)*returned x) (g:=euler)
        (((momentContinuous.const_mul (frequency:ℂ)).add
          (returnedContinuous.const_mul (1/2:ℂ))).intervalIntegrable (-q) q)
        (eulerContinuous.intervalIntegrable (-q) q),
        intervalIntegral.integral_add (f:=fun x=>(frequency:ℂ)*moment x)
          (g:=fun x=>(1/2:ℂ)*returned x)
          ((momentContinuous.const_mul (frequency:ℂ)).intervalIntegrable (-q) q)
          ((returnedContinuous.const_mul (1/2:ℂ)).intervalIntegrable (-q) q),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    _=∫ x:ℝ in (-q)..q,density x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [moment,returned,euler,density,eulerRaw]
      ring
    _=_ := by
      rw [integral]
      dsimp only [primitive]
      push_cast
      ring

theorem eulerAmbient_mean (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (actualDerivative : ∀ x:ℝ,HasDerivAt raw (derivative x) x)
    (stateRead : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    burnolQuarterMeanCoefficient (eulerAmbient raw derivative rawContinuous derivativeContinuous)=
      (raw q+raw (-q))/2 := by
  have state_eq : (state:BurnolQuarterIntervalL2)=Constructor.compact raw rawContinuous := by
    apply Lp.ext
    exact stateRead.trans (Constructor.compact_read raw rawContinuous).symm
  have meanZero:=Constructor.mean_zero state
  rw [state_eq,Constructor.mean_compact] at meanZero
  have rawIntegral : (∫ x:ℝ in (-q)..q,raw x)=0 := by
    have twoNonzero : (2:ℂ)≠0 := by norm_num
    exact (mul_eq_zero.mp meanZero).resolve_left twoNonzero
  let primitive:=fun x:ℝ=>(x:ℂ)*raw x
  let density:=fun x:ℝ=>raw x+(x:ℂ)*derivative x
  have generated (x : ℝ) : HasDerivAt primitive (density x) x := by
    convert! (Complex.ofRealCLM.hasDerivAt (x:=x)).mul (actualDerivative x) using 1
    simp only [density,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul]
  have densityContinuous : Continuous density := by
    dsimp only [density]
    fun_prop
  have integral:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _=>generated x) (densityContinuous.intervalIntegrable (-q) q)
  have value : (∫ x:ℝ in (-q)..q,eulerRaw raw derivative x)=
      (∫ x:ℝ in (-q)..q,density x)-(1/2:ℂ)*(∫ x:ℝ in (-q)..q,raw x) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (densityContinuous.intervalIntegrable (-q) q)
        ((rawContinuous.const_mul (1/2:ℂ)).intervalIntegrable (-q) q)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [eulerRaw,density]
    ring
  unfold eulerAmbient
  rw [Constructor.mean_compact,value,integral,rawIntegral,mul_zero,sub_zero]
  dsimp only [primitive]
  push_cast
  ring

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
