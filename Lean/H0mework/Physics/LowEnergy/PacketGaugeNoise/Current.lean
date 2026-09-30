import H0mework.Physics.LowEnergy.PacketGaugeNoise.Source

/-! The complete primitive current is affine in the actual gauge field.
Both ordered terms are retained on the full carrier. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise PacketFourier GaugeGreen GaugeHistory
open Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction GaugeGreen.gaugePotential boundaryAction phaseShift
  sourceHamiltonian conjugateHamiltonian

def currentVariation (gauge : GaugeProfile) (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction.comp ((phaseShift shift).toContinuousLinearMap.comp (GaugeGreen.gaugePotential gauge))+
      (GaugeGreen.gaugePotential gauge).adjoint.comp ((phaseShift shift).toContinuousLinearMap.comp boundaryAction))

theorem currentVariation_apply (gauge : GaugeProfile) (shift : Position) (field : FullMatterL2) :
    currentVariation gauge shift field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (phaseShift shift (GaugeGreen.gaugePotential gauge field))+
        (GaugeGreen.gaugePotential gauge).adjoint (phaseShift shift (boundaryAction field))) := rfl

def currentFamily (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (phaseShift shift (variedHamiltonian gauge epsilon field))+
      variedAdjointHamiltonian gauge epsilon (phaseDomain shift (boundaryDomain field)))

theorem currentFamily_original (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position)
    (field : Quantum.Generator.domain freeAction) :
    currentFamily gauge epsilon shift field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (phaseShift shift (primitiveHamiltonian gauge epsilon field))+
        variedAdjointHamiltonian gauge epsilon (phaseDomain shift (boundaryDomain field))) := by
  rw [primitiveHamiltonian_source]
  rfl

theorem currentFamily_affine (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position)
    (field : Quantum.Generator.domain freeAction) :
    currentFamily gauge epsilon shift field=phaseCurrentField shift 0 field+
      (epsilon : ℂ) • currentVariation gauge shift field.val := by
  rw [currentFamily,phaseCurrentField_zero,currentVariation_apply,
    variedHamiltonian,variedAdjointHamiltonian]
  simp only [map_add,map_smul]
  change (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (phaseShift shift (sourceHamiltonian field))+
      (epsilon : ℂ) • boundaryAction (phaseShift shift (GaugeGreen.gaugePotential gauge field.val))+
      (conjugateHamiltonian (phaseDomain shift (boundaryDomain field))+
        (epsilon : ℂ) • (GaugeGreen.gaugePotential gauge).adjoint (phaseShift shift (boundaryAction field.val))))=_
  module

theorem currentVariation_pair (gauge : GaugeProfile) (shift : Position) (left right : FullMatterL2) :
    inner ℂ (currentVariation gauge shift left) right=
      inner ℂ left (currentVariation gauge (-shift) right) := by
  have first : inner ℂ (boundaryAction (phaseShift shift (GaugeGreen.gaugePotential gauge left))) right=
      inner ℂ left ((GaugeGreen.gaugePotential gauge).adjoint (phaseShift (-shift) (boundaryAction right))) := by
    rw [boundaryAction_symmetric,phase_pair,ContinuousLinearMap.adjoint_inner_right]
  have second : inner ℂ ((GaugeGreen.gaugePotential gauge).adjoint (phaseShift shift (boundaryAction left))) right=
      inner ℂ left (boundaryAction (phaseShift (-shift) (GaugeGreen.gaugePotential gauge right))) := by
    rw [ContinuousLinearMap.adjoint_inner_left,phase_pair,boundaryAction_symmetric]
  have real : (starRingEnd ℂ) (((lapse^2)⁻¹ : ℝ) : ℂ)=(((lapse^2)⁻¹ : ℝ) : ℂ) := by simp
  simp only [currentVariation_apply,inner_smul_left,inner_smul_right,
    inner_add_left,inner_add_right,real,first,second]
  exact congrArg (fun value : ℂ => (((lapse^2)⁻¹ : ℝ) : ℂ)*value) (add_comm _ _)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
