import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageWholeForcing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageCompleteReturn
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumStaticVoltageSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumCausalPoleResponse
open PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open scoped Matrix BigOperators

@[local simp] private theorem momentum_one (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 1=spatial 0:=rfl
@[local simp] private theorem momentum_two (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 2=spatial 1:=rfl
@[local simp] private theorem momentum_three (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 3=spatial 2:=rfl

private def rampLiftTerms : List SourceTerm :=
  [⟨20,0,⟨1,0,0,0⟩,1⟩,⟨8,0,⟨0,0,0,0⟩,-1⟩,
   ⟨264,0,⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨276,0,⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨288,0,⟨1,0,0,1⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩]

/-- The complete source fold retains the scalar time-ramp, Gauss and eight matter rows, and the initial cosource. -/
def sourceVoltageRampTerms : List SourceTerm := [
  ⟨4,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨4,0,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨4,0,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨4,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨7,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨7,0,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨7,0,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨7,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨8,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(12/25:ℚ)⟩⟩⟩,
  ⟨8,0,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨8,0,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨8,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨20,0,⟨1,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨20,0,⟨1,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨20,0,⟨1,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨27,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨28,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨31,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨32,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨32,0,⟨2,1,0,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨39,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨40,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨43,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨44,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨44,0,⟨2,0,1,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨51,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨52,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩⟩,
  ⟨55,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩⟩,
  ⟨56,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩⟩,
  ⟨56,0,⟨2,0,0,1⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩⟩,
  ⟨74,0,⟨1,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨76,0,⟨1,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨80,0,⟨1,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨82,0,⟨1,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨98,0,⟨1,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨100,0,⟨1,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨104,0,⟨1,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨106,0,⟨1,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩]

private theorem ramp_certificate :
    fastNormalizeTerms (productTerms originalJacobiTerms rampLiftTerms++negativeTerms sourceVoltageRampTerms)=[] := by
  decide +kernel

private theorem lapse_coefficient : (6/25:ℂ)*rootTwo*rootFifteen=2*(lapse:ℂ) := by
  have two : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have fifteen : (Real.sqrt 15)^2=15:=Real.sq_sqrt (by norm_num)
  have positive : 0≤(3/25:ℝ)*Real.sqrt 2*Real.sqrt 15:=by positivity
  have equal : (3/25:ℝ)*Real.sqrt 2*Real.sqrt 15=lapse:=by
    nlinarith [lapse_sq,lapse_pos,mul_self_nonneg ((3/25:ℝ)*Real.sqrt 2*Real.sqrt 15-lapse)]
  unfold rootTwo rootFifteen
  have h:=congrArg (fun x : ℝ=>(x:ℂ)) equal
  push_cast at h
  linear_combination 2*h

private theorem rampLift_value (spatial : Fin 3→ℂ) (z : ℂ) :
    sourceMatrix rampLiftTerms (fullMomentum spatial z)*ᵥPi.single 0 1=
      z • sourceVoltageSpatialVector spatial+sourceVoltageTemporalVector := by
  ext i
  norm_num [rampLiftTerms,sourceMatrix,SourceTerm.matrix,Powers.value,fullMomentum,
    Matrix.add_mulVec,Matrix.single_mulVec,Matrix.mulVec_single,Matrix.col,Matrix.add_apply,
    Matrix.single_apply,Pi.single_apply,Matrix.single,eq_comm,coefficientValue,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,sourceVoltageSpatialVector,
    sourceVoltageTemporalVector,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  rw [←lapse_coefficient]
  split_ifs <;> try omega
  all_goals norm_num <;> ring

/-- The original full Jacobi operator acts on the actual voltage ramp numerator, in all 289 rows. -/
theorem sourceVoltageRamp_equation (spatial : Fin 3→ℂ) (z : ℂ) :
    originalJacobi (fullMomentum spatial z)*ᵥ(z • sourceVoltageSpatialVector spatial+sourceVoltageTemporalVector)=
      sourceMatrix sourceVoltageRampTerms (fullMomentum spatial z)*ᵥPi.single 0 1 := by
  have generated:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥPi.single 0 1)
    (normalization_equal (productTerms originalJacobiTerms rampLiftTerms) sourceVoltageRampTerms
      ramp_certificate (fullMomentum spatial z))
  rw [productTerms_value,←Matrix.mulVec_mulVec,rampLift_value] at generated
  exact generated

/-- Re(z)>0 will provide the half-axis Laplace integral; the algebra keeps every nonzero spectral point. -/
def sourceVoltageLaplaceRamp (spatial : Fin 3→ℂ) (z : ℂ) : Fin 289→ℂ :=
  z⁻¹ • sourceVoltageSpatialVector spatial+(z⁻¹)^2 • sourceVoltageTemporalVector

def sourceVoltageLaplaceForcing (spatial : Fin 3→ℂ) (z : ℂ) : Fin 289→ℂ :=
  (z⁻¹)^2 • (sourceMatrix sourceVoltageRampTerms (fullMomentum spatial z)*ᵥPi.single 0 1)

theorem sourceVoltageLaplaceRamp_equation (spatial : Fin 3→ℂ) (z : ℂ) (nonzero : z≠0) :
    originalJacobi (fullMomentum spatial z)*ᵥsourceVoltageLaplaceRamp spatial z=
      sourceVoltageLaplaceForcing spatial z := by
  have same : sourceVoltageLaplaceRamp spatial z=(z⁻¹)^2 •
      (z • sourceVoltageSpatialVector spatial+sourceVoltageTemporalVector) := by
    rw [sourceVoltageLaplaceRamp,smul_add,smul_smul]
    congr 1
    congr 1
    field_simp [nonzero]
  rw [same,Matrix.mulVec_smul,sourceVoltageRamp_equation]
  rfl

end LowEnergy.PreparationPhysicalVoltageCompleteReturn
