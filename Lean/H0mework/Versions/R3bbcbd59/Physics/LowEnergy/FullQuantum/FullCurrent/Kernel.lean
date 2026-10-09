import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrent.Source
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.TriangularDirac
import H0mework.Versions.AB.Physics.LowEnergyFullPhase.Derivative

/-! The two inverse domains belong to the same original Dirac operator under
its already generated phase change. The dual leg retains (-z,-k). -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction StageNineCurrentCoframeMatterTemporalPrincipal
open StateResponse
noncomputable section

def stationaryKernel (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  Triangular.diracKernel actual point k z+
    (-Complex.I*(frequency : ℂ)) •
      (currentCoframeMatterTemporalPrincipal (actual.coframe point)*FullPhase.phaseGenerator)

theorem stationaryKernel_original_clock (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (v : DiracExteriorMatterCarrier) :
    stationaryKernel point k z v=Triangular.diracKernel actual point k z v+
      currentCoframeMatterTemporalPrincipal (actual.coframe point)
        (FullPhase.phaseVelocity FullPhase.sixPrimalRate FullPhase.otherRate 0 v) := by
  rw [FullPhase.primal_velocity,FullPhase.primal_zero]
  simp only [stationaryKernel,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LinearMap.id_apply,map_smul]

def stationaryGreen (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  Ring.inverse (stationaryKernel point k z)

theorem stationaryGreen_two_sided (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (regular : IsUnit (stationaryKernel point k z)) :
    stationaryKernel point k z*stationaryGreen point k z=1 ∧
      stationaryGreen point k z*stationaryKernel point k z=1 :=
  ⟨Ring.mul_inverse_cancel _ regular,Ring.inverse_mul_cancel _ regular⟩

theorem full_source_Euler_and_current (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (regularPlus : IsUnit (stationaryKernel point k z))
    (regularMinus : IsUnit (stationaryKernel point (-k) (-z)))
    (Bplus Czero Cminus Bzero J : Mother) :
    stationaryKernel point k z (primalResponse (lapse : ℂ)⁻¹ (stationaryGreen point k z) Czero (actual.matter point))=
        -(lapse : ℂ)⁻¹ • Czero (actual.matter point) ∧
    (∀ v, dualResponse (lapse : ℂ)⁻¹ (actual.conjugateMatter point) Cminus (stationaryGreen point (-k) (-z))
      (stationaryKernel point (-k) (-z) v)=-(lapse : ℂ)⁻¹*actual.conjugateMatter point (Cminus v)) ∧
    (lapse : ℂ)*(actual.conjugateMatter point (Bplus (primalResponse (lapse : ℂ)⁻¹
        (stationaryGreen point k z) Czero (actual.matter point)))+
      dualResponse (lapse : ℂ)⁻¹ (actual.conjugateMatter point) Cminus (stationaryGreen point (-k) (-z))
        (Bzero (actual.matter point))+actual.conjugateMatter point (J (actual.matter point)))=
      (4*Complex.I)*transferNativeRead point (nativeResponseWord point Bplus Czero Cminus Bzero
        (stationaryGreen point k z) (stationaryGreen point (-k) (-z)) J) := by
  refine ⟨primalResponse_equation _ _ _ _ _ (stationaryGreen_two_sided point k z regularPlus).1,?_,?_⟩
  · intro v
    exact dualResponse_equation _ _ _ _ _ _ (stationaryGreen_two_sided point (-k) (-z) regularMinus).2
  · exact original_response_native _ _ _ _ _ _ _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrent
