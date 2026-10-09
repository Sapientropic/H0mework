import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource
open PreparationPhysicalChannelRadialJet CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform

open ActualEMCarrierOwn
theorem checked_em_inverse_schwartz_apply (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emInverseSchwartz test x = emPacket test x  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply test x

theorem checked_em_spatial_newton_schwartz_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun k=>‖test k‖/Real.sqrt (spatialSquare k))  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable test

theorem checked_em_spatial_newton_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun y=>(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y))  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable test x

theorem checked_em_newton_massless_convolution (kappa : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa 0 test x=
      ∫y : PhysicalMomentum,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y)  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution kappa test x

theorem checked_inverse_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) : Integrable (emPacket test) := by
  have paid:=(emInverseSchwartz test).integrable (μ:=volume)
  have same : (emInverseSchwartz test : PhysicalMomentum→ℂ)=emPacket test := by
    funext x
    exact em_inverse_schwartz_apply test x
  rw [←same]
  exact paid

theorem checked_auxiliary_kappa_independent (kappa other : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa 0 test x=emNewtonPacket other 0 test x := by
  rw [em_newton_massless_convolution,em_newton_massless_convolution]

theorem checked_inverse_zero : emInverseSchwartz (0:𝓢(PhysicalMomentum,ℂ))=0 := by
  ext x
  rw [em_inverse_schwartz_apply]
  simp [emPacket]

theorem checked_origin_totalization (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare (0:PhysicalMomentum)):ℂ))⁻¹*emPacket test (x-0)=0 := by
  simp [spatialSquare]

theorem checked_origin_null_measure : ∀ᵐ y : PhysicalMomentum ∂volume,y≠0 := volume.ae_ne 0

theorem checked_fourpi_not_repeated :
    (4*(Real.pi:ℂ))⁻¹≠((4*(Real.pi:ℂ))^2)⁻¹ := by
  intro same
  have denominator:=inv_injective same
  have real:=congrArg Complex.re denominator
  norm_num [pow_two] at real
  have strong : (1:ℝ)<4*Real.pi := by linarith [Real.pi_gt_three]
  have product : (0:ℝ)<(4*Real.pi)*(4*Real.pi-1) := mul_pos (by linarith) (by linarith)
  nlinarith [product]

theorem checked_original_phase (frequency x : PhysicalMomentum) :
    sourceSpatialPhase frequency x=Complex.exp (Complex.I*((∑j:Fin 3,(2*Real.pi)*frequency j*x j:ℝ):ℂ)) := rfl

theorem checked_nonempty_radial : (𝓝[>] (0:ℝ)).NeBot := inferInstance

end LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit

