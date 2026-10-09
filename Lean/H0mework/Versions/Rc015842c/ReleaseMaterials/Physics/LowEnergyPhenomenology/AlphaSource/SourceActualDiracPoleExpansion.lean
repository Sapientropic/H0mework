import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedScatteringReturn

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.Triangular
open StageNineCurrentCoframeMatterTemporalPrincipal PreparationPhysicalJointRotationCharge
open PreparationVacuumElectromagneticIdentity PreparationPhysicalJointGeneratorEnergyReturn
open scoped InnerProductSpace BigOperators Matrix

/-- Coordinates of the original temporal-principal inverse, with its actual chirality order. -/
def sourceInverseTemporalValues (v : Source.Index→ℂ) : Source.Index→ℂ :=
  coordinates (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) (embed v))

private theorem time_surjective : Function.Surjective (Matrix.mulVecLin sourceTimeMatrix) := by
  apply LinearMap.surjective_of_injective
  intro a b same
  have transformed:=congrArg (fun v=>currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) (embed v)) same
  simp only [Matrix.mulVecLin_apply,←sourceTimeMatrix_original,
    currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic 0)] at transformed
  simpa only [coordinates_embed] using congrArg coordinates transformed

theorem sourceInverseTemporalValues_original (v : Source.Index→ℂ) :
    currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) (embed v)=
      embed (sourceInverseTemporalValues v) := by
  obtain ⟨u,same⟩:=time_surjective v
  change sourceTimeMatrix*ᵥu=v at same
  have returned : currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) (embed v)=embed u := by
    rw [←same,←sourceTimeMatrix_original]
    exact currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic 0) _
  have read : sourceInverseTemporalValues v=u := by
    rw [sourceInverseTemporalValues,returned,coordinates_embed]
  rw [read,returned]

private theorem pole_nonzero (energy damping pole : ℝ) (positive : 0<damping) :
    Retarded.spectralParameter energy damping-(pole:ℂ)≠0 := by
  intro zero
  have imag:=congrArg Complex.im zero
  simp [Retarded.spectralParameter] at imag
  exact positive.ne' imag

/-- Each pole comes from the original full Hamiltonian eigenaction on the actual eight-source carrier. -/
theorem sourceMovingGreen_pole (p : Fin 3→ℝ) (energy damping : ℝ) (positive : 0<damping)
    (state : RestStateIndex) :
    Retarded.value 0 p energy damping (naturalCoordinates (embed (sourceMovingPoleValues p state)))=
      (Complex.I/(Retarded.spectralParameter energy damping-(sourceMovingPoleEnergy p state:ℂ))) •
        naturalCoordinates (embed (sourceMovingPoleValues p state)) := by
  have eigen:=sourceMovingPole_hamiltonian 0 p state
  simp only [Runtime.configuration_eq] at eigen
  have equation:=DFunLike.congr_fun (Retarded.value_kernel_right 0 p energy damping positive)
    (naturalCoordinates (embed (sourceMovingPoleValues p state)))
  rw [Retarded.kernel_original] at equation
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,operator_coordinates,eigen,map_smul,
    ←sub_smul] at equation
  have nonzero:=pole_nonzero energy damping (sourceMovingPoleEnergy p state) positive
  calc
    _=(Retarded.spectralParameter energy damping-(sourceMovingPoleEnergy p state:ℂ))⁻¹ •
        ((Retarded.spectralParameter energy damping-(sourceMovingPoleEnergy p state:ℂ)) •
          Retarded.value 0 p energy damping (naturalCoordinates (embed (sourceMovingPoleValues p state)))) := by
      rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    _=_ := by rw [equation,smul_smul]; congr 1; ring

/-- The coefficients are read from the original C0-inverse input; no spectral weight is supplied. -/
def sourceActualPoleCoefficient (p : Fin 3→ℝ) (v : Source.Index→ℂ) (state : RestStateIndex) : ℂ :=
  ∑index : Source.Index,star (sourceMovingPoleValues p state index)*sourceInverseTemporalValues v index

/-- The full original Dirac Green, including C0 inverse on the right, generates all eight pole branches. -/
theorem sourceActualDiracGreen_poles (p : Fin 3→ℝ) (energy damping : ℝ) (positive : 0<damping)
    (v : Source.Index→ℂ) :
    Retarded.diracValue 0 p energy damping (naturalCoordinates (embed v))=
      ∑state : RestStateIndex,
        (sourceActualPoleCoefficient p v state *
          (Complex.I/(Retarded.spectralParameter energy damping-(sourceMovingPoleEnergy p state:ℂ)))) •
            naturalCoordinates (embed (sourceMovingPoleValues p state)) := by
  rw [Retarded.diracValue_side 0 p energy damping positive,mul_apply_eq_comp,operator_coordinates,
    sourceInverseTemporalValues_original]
  conv_lhs => rw [←sourceMovingPole_complete p (sourceInverseTemporalValues v)]
  simp only [map_sum,map_smul,sourceMovingGreen_pole p energy damping positive,smul_smul,
    sourceActualPoleCoefficient]

end LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
