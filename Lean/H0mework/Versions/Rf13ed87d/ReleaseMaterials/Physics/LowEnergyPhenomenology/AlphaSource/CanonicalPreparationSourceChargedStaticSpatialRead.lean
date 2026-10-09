import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedStaticLaurent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedLongRangeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumChargedSpatialResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumObservedPoleTensor
open PreparationVacuumObservedStaticResidue PreparationVacuumStaticSimpleCoupling
open PreparationVacuumQuantumSlowResidue PreparationVacuumFullSlowFieldResponse
open PreparationVacuumWholeOrigin PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumCausalPoleResponse PreparationVacuumStaticSpatialSource
open PreparationVacuumActualSpatialPacket CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceChargedNativeFrameJet sourceActualNativeResidue sourceFullCurrentResidue
  sourceStaticCurrent sourceStaticNative sourceNativeSimple sourceCurrentSimple sourceChargedSecondField
  sourceFrequencyPacket

/-- The full tensor numerator of the static double coefficient, before any angular or material restriction. -/
def sourceChargedDoubleGreenNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3,((sourceChargedSpatialCoefficient i:ℂ)⁻¹*
    sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) • sourceChargedChannel n 0 i

/-- All three inverse spatial prices multiply their actual source forcing and frame jets. -/
def sourceChargedSimpleGreenNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3, (((sourceChargedSpatialCoefficient i:ℂ)⁻¹*
    sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩) • sourceChargedChannel n 0 i+
    ((sourceChargedSpatialCoefficient i:ℂ)⁻¹*sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) •
      sourceChargedChannel 0 1 i)

theorem sourceChargedStaticDouble_green (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    sourceChargedStaticDouble q n l r=(spatialSquare n:ℂ)⁻¹ • sourceChargedDoubleGreenNumerator q n l r+
      sourceRegularMatrix 0*ᵥsourceStaticCurrent q n l r := by
  simp only [sourceChargedStaticDouble,sourceChargedDoubleGreenNumerator,sourceChargedDenominator,
    zero_pow (by decide : 2≠0),mul_zero,add_zero,mul_inv_rev,Finset.smul_sum,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem sourceChargedStaticSimple_green (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    sourceChargedStaticSimple q n l r=(spatialSquare n:ℂ)⁻¹ • sourceChargedSimpleGreenNumerator q n l r+
      sourceRegularMatrix 0*ᵥsourceCurrentSimple q n l r := by
  simp only [sourceChargedStaticSimple,sourceChargedSimpleGreenNumerator,sourceChargedDenominator,
    zero_pow (by decide : 2≠0),mul_zero,add_zero,mul_inv_rev,Finset.smul_sum,smul_add,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1 <;> congr 1 <;> ring

theorem sourceChargedChannel_spatial_scale (n : PhysicalMomentum) (s : ℝ) (i : Fin 3) :
    sourceChargedChannel (s • n) 0 i=(s:ℂ) • sourceChargedChannel n 0 i := by
  rw [sourceChargedChannel,sourceStaticMomentum_radial]
  simp only [sourceChargedNativeFrameJet,sourceLinearPart,degreeTensor_scaled,pow_one,
    smul_mul_assoc,mul_smul_comm,←smul_sub,Matrix.smul_mulVec,sourceChargedChannel]

private theorem static_native_scale (q : PhysicalResponsePoint) (n : PhysicalMomentum) (s : ℝ)
    (positive : 0<s) (l r : RestStateIndex) :
    sourceStaticNative q (s • n) l r=(s:ℂ) • sourceStaticNative q n l r := by
  simp only [sourceStaticNative,sourceStaticMomentum_radial,sourceReaderFirst_radial,
    sourceStaticCurrent_radial q n s positive,Matrix.smul_mulVec]

theorem sourceChargedDoubleGreenNumerator_scale (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceChargedDoubleGreenNumerator q (s • n) l r=(s:ℂ)^2 • sourceChargedDoubleGreenNumerator q n l r := by
  simp only [sourceChargedDoubleGreenNumerator,static_native_scale q n s positive,sourceSlowRead_smul,
    sourceChargedChannel_spatial_scale,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem sourceChargedSimpleGreenNumerator_scale (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceChargedSimpleGreenNumerator q (s • n) l r=(s:ℂ) • sourceChargedSimpleGreenNumerator q n l r := by
  simp only [sourceChargedSimpleGreenNumerator,static_native_scale q n s positive,sourceSlowRead_smul,
    sourceNativeSimple_radial q n s positive,sourceChargedChannel_spatial_scale,Pi.smul_apply,smul_eq_mul,
    Finset.smul_sum,smul_add,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1 <;> congr 1 <;> ring

/-- Radial degree is generated from the original forcing and frame jets, with the regular term retained. -/
theorem sourceChargedStatic_radial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (l r : RestStateIndex) :
    sourceChargedStaticDouble q (s • n) l r=sourceChargedStaticDouble q n l r ∧
    sourceChargedStaticSimple q (s • n) l r=(s:ℂ)⁻¹ • sourceChargedStaticSimple q n l r := by
  have nonzero : (s:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  constructor
  · rw [sourceChargedStaticDouble_green,sourceChargedStaticDouble_green,sourceChargedDoubleGreenNumerator_scale q n s positive,
      sourceSpatialSquare_radial,sourceStaticCurrent_radial q n s positive]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_inv_rev,smul_smul]
    congr 2
    field_simp
  · rw [sourceChargedStaticSimple_green,sourceChargedStaticSimple_green,sourceChargedSimpleGreenNumerator_scale q n s positive,
      sourceSpatialSquare_radial,sourceCurrentSimple_radial q n s positive]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_inv_rev,smul_smul,smul_add,Matrix.mulVec_smul]
    congr 1
    congr 1
    field_simp

/-- The original independently amputated detector consumes the generated simple static field. -/
def sourceChargedStaticResponse (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℂ :=
  sourceChargedRead q pL pR a b (sourceChargedStaticSimple q n l r)

theorem sourceChargedStaticResponse_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(sourceChargedRead q pL pR a b (sourceChargedSecondField q n (eta:ℂ) l r)-
      ((eta:ℂ)⁻¹)^2*sourceChargedRead q pL pR a b (sourceChargedStaticDouble q n l r)))
      (𝓝[>] 0) (𝓝 (sourceChargedStaticResponse q n l r a b pL pR)) := by
  have result := (sourceChargedRead q pL pR a b).continuous.continuousAt.tendsto.comp
    (sourceChargedStaticSimple_generated q n spatial l r)
  simpa only [Function.comp_def,map_smul,map_sub,smul_eq_mul,sourceChargedStaticResponse] using result

/-- This coefficient belongs to the actual Green multiplier; neither its angle nor its material tensor is averaged. -/
theorem sourceChargedStaticResponse_green (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceChargedStaticResponse q n l r a b pL pR=
      (spatialSquare n:ℂ)⁻¹*sourceChargedRead q pL pR a b (sourceChargedSimpleGreenNumerator q n l r)+
        sourceChargedRead q pL pR a b (sourceRegularMatrix 0*ᵥsourceCurrentSimple q n l r) := by
  rw [sourceChargedStaticResponse,sourceChargedStaticSimple_green,map_add,map_smul,smul_eq_mul]

def sourceChargedStaticPacketKernel (q : PhysicalResponsePoint) (frequency : FullQuantum.FullSpace.Position)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase (fun j=>frequency j) position*sourcePacketIndependentVertex q pL pR a b frequency
    (sourceChargedFieldPart (sourceChargedStaticSimple q (FullQuantum.FullSpace.physicalMomentum frequency) l r))

/-- The physical Fourier momentum and both original unit-ball packet legs consume the same Green coefficient. -/
theorem sourceChargedStaticPacketKernel_green (q : PhysicalResponsePoint) (frequency : FullQuantum.FullSpace.Position)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    sourceChargedStaticPacketKernel q frequency l r a b pL pR position=
      sourceSpatialPhase (fun j=>frequency j) position*(star (sourceFrequencyPacket frequency)*sourceFrequencyPacket frequency)*
        ((spatialSquare (FullQuantum.FullSpace.physicalMomentum frequency):ℂ)⁻¹*
          sourceChargedRead q pL pR a b (sourceChargedSimpleGreenNumerator q (FullQuantum.FullSpace.physicalMomentum frequency) l r)+
          sourceChargedRead q pL pR a b (sourceRegularMatrix 0*ᵥsourceCurrentSimple q (FullQuantum.FullSpace.physicalMomentum frequency) l r)) := by
  rw [sourceChargedStaticPacketKernel,sourcePacketIndependentVertex_generated,←sourceChargedRead_original,
    ←sourceChargedStaticResponse,sourceChargedStaticResponse_green]
  ring

/-- The eta coefficient is formed at each actual Fourier momentum before the original spatial read. -/
theorem sourceChargedStaticPacketKernel_generated (q : PhysicalResponsePoint) (frequency : FullQuantum.FullSpace.Position)
    (spatial : 0<spatialSquare (FullQuantum.FullSpace.physicalMomentum frequency))
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*sourceSpatialPhase (fun j=>frequency j) position*
      (sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceChargedSecondField q (FullQuantum.FullSpace.physicalMomentum frequency) (eta:ℂ) l r))-
        ((eta:ℂ)⁻¹)^2*sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
          (sourceChargedStaticDouble q (FullQuantum.FullSpace.physicalMomentum frequency) l r))))
      (𝓝[>] 0) (𝓝 (sourceChargedStaticPacketKernel q frequency l r a b pL pR position)) := by
  have generated := (sourceChargedStaticResponse_generated q (FullQuantum.FullSpace.physicalMomentum frequency)
    spatial l r a b pL pR).const_mul
    (sourceSpatialPhase (fun j=>frequency j) position*(star (sourceFrequencyPacket frequency)*sourceFrequencyPacket frequency))
  simp only [sourceChargedStaticPacketKernel,sourcePacketIndependentVertex_generated,
    sourceChargedStaticResponse,sourceChargedRead_original] at generated ⊢
  convert generated using 1
  · funext eta
    ring
  · congr 1
    ring

end LowEnergy.PreparationVacuumChargedLongRangeRead
