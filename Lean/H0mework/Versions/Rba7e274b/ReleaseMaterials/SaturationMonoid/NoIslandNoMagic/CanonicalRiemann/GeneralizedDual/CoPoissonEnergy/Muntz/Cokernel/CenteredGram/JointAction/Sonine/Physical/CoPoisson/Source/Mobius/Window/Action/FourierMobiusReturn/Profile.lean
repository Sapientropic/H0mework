import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.ZeroEndpoint
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.RadialReturn
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OriginalRieszSource

def gluedSourceRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x|≤4 then sourceH coordinate x else
    (4:ℂ)^(star coordinate.value)*((|x|:ℝ):ℂ)^(-star coordinate.value)*sourceH coordinate 4

def gluedPowerRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x|≤4 then 1 else (4:ℂ)^(star coordinate.value)*((|x|:ℝ):ℂ)^(-star coordinate.value)

def fixedEdgeReturnRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -(2:ℂ)*((|x|:ℝ):ℂ)^(-star coordinate.value)*edgeResponsePrimitive coordinate (min |x| 4)

def generatedFourierReturnRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  2*gluedSourceRaw coordinate x+Kernel.beta coordinate*fixedEdgeReturnRaw coordinate x+
    (2*sourceSigma*sourceGamma coordinate/star coordinate.value)*gluedPowerRaw coordinate x

 theorem response_positive_clamped_integral (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    (∫ t : ℝ in Ioc 0 x,(t:ℂ)^(star coordinate.value-1)*generatedFourierMobiusRaw coordinate t)=
      fourierResponsePrimitive coordinate (min x 4) := by
  unfold generatedFourierMobiusRaw fourierResponsePrimitive
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤min x 4)]
  have equality : (Ioc (0:ℝ) x).indicator (fun t=>(t:ℂ)^(star coordinate.value-1)*
      (symmetricInterval 4).indicator (fun y=>Kernel.beta coordinate*sourceEdge y-(y:ℂ)*sourceHprime coordinate y-
        star coordinate.value*sourceH coordinate y-sourceSigma*sourceGamma coordinate) t)=
      (Ioc (0:ℝ) (min x 4)).indicator (fun t=>(t:ℂ)^(star coordinate.value-1)*
        (Kernel.beta coordinate*sourceEdge t-(t:ℂ)*sourceHprime coordinate t-
          star coordinate.value*sourceH coordinate t-sourceSigma*sourceGamma coordinate)) := by
    funext t
    by_cases below : 0<t
    · by_cases first : t≤x
      · by_cases second : t≤4
        · simp only [indicator_of_mem (show t∈Ioc 0 x from ⟨below,first⟩),
            indicator_of_mem (show t∈symmetricInterval 4 from ⟨by linarith,second⟩),
            indicator_of_mem (show t∈Ioc 0 (min x 4) from ⟨below,le_min first second⟩)]
        · simp only [indicator_of_mem (show t∈Ioc 0 x from ⟨below,first⟩),
            indicator_of_notMem (show t∉symmetricInterval 4 from fun i=>second i.2),mul_zero,
            indicator_of_notMem (show t∉Ioc 0 (min x 4) from fun i=>second (le_trans i.2 (min_le_right _ _)))]
      · simp only [indicator_of_notMem (show t∉Ioc 0 x from fun i=>first i.2),
          indicator_of_notMem (show t∉Ioc 0 (min x 4) from fun i=>first (le_trans i.2 (min_le_left _ _)))]
    · simp only [indicator_of_notMem (show t∉Ioc 0 x from fun i=>below i.1),
        indicator_of_notMem (show t∉Ioc 0 (min x 4) from fun i=>below i.1)]
  rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc,equality]

 theorem computed_positive_return_profile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    -(2:ℂ)*(x:ℂ)^(-star coordinate.value)*
      (∫ t : ℝ in Ioc 0 x,(t:ℂ)^(star coordinate.value-1)*generatedFourierMobiusRaw coordinate t)=
        generatedFourierReturnRaw coordinate x := by
  rw [response_positive_clamped_integral coordinate x positive,actual_fourier_response_primitive coordinate _ (by positivity)]
  unfold generatedFourierReturnRaw fixedEdgeReturnRaw gluedSourceRaw gluedPowerRaw
  rw [abs_of_pos positive]
  by_cases inside : x≤4
  · rw [min_eq_left inside,if_pos inside,if_pos inside]
    have inverse : (x:ℂ)^(-star coordinate.value)*(x:ℂ)^(star coordinate.value)=1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),neg_add_cancel,Complex.cpow_zero]
    ring_nf
    rw [inverse]
    ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge inside)),if_neg inside,if_neg inside]
    norm_num only [Complex.ofReal_ofNat]
    ring

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
