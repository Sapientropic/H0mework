import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualScatteringPoleLegs

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing FullQuantum FullSpace FullQuantum.Triangular
open PreparationPhysicalJointRotationCharge PreparationVacuumElectromagneticIdentity
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalChargedPacketQuantumReturn PreparationVacuumPhysicalQuantumLockedCharge
open StageNineCurrentCoframeMatterTemporalPrincipal ChargedPreparation.Dynamics
open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix Topology

private theorem time_charged_values (side edge : Fin 2) :
    sourceTimeMatrix*ᵥsourceRestStateValues (sourceChargedRestIndex side edge)=
      (Complex.I*(lapse:ℂ)⁻¹*sourceRestSign side) • sourceRestStateValues (sourceChargedRestIndex (1-side) edge) := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    simp [sourceTimeMatrix,sourceRestStateValues,sourceChargedRestIndex,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,ChargedPreparation.SpatialSpectrum.lowerValues,
      Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_four,diracGammaZero,sourceRestSign]

private theorem time_charged (side edge : Fin 2) :
    currentCoframeMatterTemporalPrincipal (actual.coframe 0) (sourceChargedRestriction side edge)=
      (Complex.I*(lapse:ℂ)⁻¹*sourceRestSign side) • sourceChargedRestriction (1-side) edge := by
  simp only [sourceChargedRestriction,actualRestState_source,actualRestStateCoordinates,
    map_smul,sourceTimeMatrix_original,time_charged_values]
  exact smul_comm _ _ _

/-- The original C0 inverse switches the actual charged chiral maker; its source factor is retained. -/
theorem sourceActualChargedTemporalInverse (side edge : Fin 2) :
    currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) (sourceChargedRestriction side edge)=
      (Complex.I*(lapse:ℂ)*sourceRestSign side) • sourceChargedRestriction (1-side) edge := by
  have twice : (1-(1-side):Fin 2)=side := by fin_cases side <;> rfl
  have inverse:=currentCoframeMatterTemporalPrincipalInverse_left (actual.coframe 0)
    (actual_noncharacteristic 0) ((Complex.I*(lapse:ℂ)*sourceRestSign side) • sourceChargedRestriction (1-side) edge)
  rw [map_smul,time_charged,twice,smul_smul] at inverse
  have scalar : (Complex.I*(lapse:ℂ)*sourceRestSign side)*
      (Complex.I*(lapse:ℂ)⁻¹*sourceRestSign (1-side))=1 := by
    have nonzero : (lapse:ℂ)≠0:=Complex.ofReal_ne_zero.mpr lapse_pos.ne'
    fin_cases side <;> norm_num [sourceRestSign]
    all_goals field_simp
    all_goals simp
  rw [scalar,one_smul] at inverse
  exact inverse

/-- The charged maker's rest energy is read from its actual original triplet pole. -/
def sourceActualChargedRestEnergy (side : Fin 2) : ℝ :=
  (if side=0 then -1 else 1)*3*frequency

private theorem charged_energy (side edge : Fin 2) :
    sourceRestPoleEnergy (sourceRestStatePole (sourceChargedRestIndex side edge))=
      (sourceActualChargedRestEnergy side:ℂ) := by
  fin_cases side <;> fin_cases edge <;>
    simp [sourceRestPoleEnergy,sourceRestStatePole,sourceChargedRestIndex,sourceRestSign,
      sourceRestSymmetry,sourceActualChargedRestEnergy]
  all_goals ring

theorem sourceActualChargedRest_hamiltonian (side edge : Fin 2) :
    FullQuantum.hamiltonian actual 0 0 (sourceChargedRestriction side edge)=
      (sourceActualChargedRestEnergy side:ℂ) • sourceChargedRestriction side edge := by
  rw [sourceChargedRestriction,actualRestState_source]
  have projected : sourceRestPoleProjection (sourceRestStatePole (sourceChargedRestIndex side edge))*ᵥ
      actualRestStateCoordinates 0 (sourceChargedRestIndex side edge)=
        actualRestStateCoordinates 0 (sourceChargedRestIndex side edge) := by
    rw [actualRestStateCoordinates,Matrix.mulVec_smul,sourceRestState_projection]
  have generated:=sourceRestPoleProjection_physical (sourceRestStatePole (sourceChargedRestIndex side edge)) 0
    (actualRestStateCoordinates 0 (sourceChargedRestIndex side edge))
  simpa only [projected,Runtime.configuration_eq,charged_energy] using generated

/-- The complete original resolvent on the charged rest maker keeps its own physical pole. -/
theorem sourceActualChargedRest_value (side edge : Fin 2) (energy damping : ℝ) (positive : 0<damping) :
    Retarded.value 0 0 energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      (Complex.I/(Retarded.spectralParameter energy damping-(sourceActualChargedRestEnergy side:ℂ))) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
  have nonzero : Retarded.spectralParameter energy damping-(sourceActualChargedRestEnergy side:ℂ)≠0 := by
    intro zero
    have imag:=congrArg Complex.im zero
    simp [Retarded.spectralParameter] at imag
    exact positive.ne' imag
  have equation:=DFunLike.congr_fun (Retarded.value_kernel_right 0 0 energy damping positive)
    (naturalCoordinates (sourceChargedRestriction side edge))
  rw [Retarded.kernel_original] at equation
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,operator_coordinates,
    sourceActualChargedRest_hamiltonian,map_smul,←sub_smul] at equation
  calc
    _=(Retarded.spectralParameter energy damping-(sourceActualChargedRestEnergy side:ℂ))⁻¹ •
      ((Retarded.spectralParameter energy damping-(sourceActualChargedRestEnergy side:ℂ)) •
        Retarded.value 0 0 energy damping (naturalCoordinates (sourceChargedRestriction side edge))) := by
      rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    _=_ := by rw [equation,smul_smul]; congr 1; ring

/-- The Dirac preparation pole includes its actual C0-inverse chirality and coefficient, once. -/
theorem sourceActualChargedRest_dirac (side edge : Fin 2) (energy damping : ℝ) (positive : 0<damping) :
    Retarded.diracValue 0 0 energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      ((-(lapse:ℂ)*sourceRestSign side)/(Retarded.spectralParameter energy damping-(sourceActualChargedRestEnergy (1-side):ℂ))) •
        naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  rw [Retarded.diracValue_side 0 0 energy damping positive,mul_apply_eq_comp,operator_coordinates,
    sourceActualChargedTemporalInverse,map_smul,map_smul,sourceActualChargedRest_value _ _ _ _ positive,smul_smul]
  congr 1
  field_simp
  simp
  all_goals ring

/-- The pole residue is generated by the original Dirac family on the same actual maker input. -/
theorem sourceActualChargedRest_residue_exact (side edge : Fin 2) (damping : ℝ) (positive : 0<damping) :
    (damping:ℂ) • Retarded.diracValue 0 0 (sourceActualChargedRestEnergy (1-side)) damping
      (naturalCoordinates (sourceChargedRestriction side edge))=
        (Complex.I*(lapse:ℂ)*sourceRestSign side) • naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  rw [sourceActualChargedRest_dirac _ _ _ _ positive,smul_smul]
  congr 1
  have nonzero : (damping:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [Retarded.spectralParameter,add_sub_cancel_left]
  field_simp
  simp

theorem sourceActualChargedRest_residue (side edge : Fin 2) :
    Tendsto (fun damping : ℝ=>(damping:ℂ) •
      Retarded.diracValue 0 0 (sourceActualChargedRestEnergy (1-side)) damping
        (naturalCoordinates (sourceChargedRestriction side edge))) (𝓝[>] 0)
      (𝓝 ((Complex.I*(lapse:ℂ)*sourceRestSign side) • naturalCoordinates (sourceChargedRestriction (1-side) edge))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with damping positive
  exact (sourceActualChargedRest_residue_exact side edge damping positive).symm

end LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
