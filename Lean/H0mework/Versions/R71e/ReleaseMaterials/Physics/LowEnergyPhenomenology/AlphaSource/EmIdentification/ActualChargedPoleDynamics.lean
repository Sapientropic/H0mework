import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMVoltage
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedRestPole
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRotationMatrix

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualChargedPoleDynamics
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage10 Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNormalizedFullField PreparationPhysicalJointRotationCharge
open PreparationPhysicalChargedScatteringPoleReturn PreparationVacuumPhysicalFeedback
open ChargedPreparation.Dynamics GaussCoreHilbert FullQuantum.FullSpace FullQuantum.Triangular
open FullQuantum FullSpace
open GaussComposite.PhysicalEMVoltage GaussComposite.PhysicalEMChargeReadout
open PreparationPhysicalActualPhaseChargeReturn
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceChargedRestriction sourceMovingFullHamiltonian

def chargedSideSign (side : Fin 2) : ℝ := if side=0 then -1 else 1

def chargedEdgeSign (edge : Fin 2) : ℝ := if edge=0 then 1 else -1

def chargedAxisMomentum (k : ℝ) : PhysicalMomentum := ![0,0,k]

def chargedEnergyDiagonal (p : PhysicalMomentum) (side edge : Fin 2) : ℝ :=
  chargedSideSign side*(3*frequency+chargedEdgeSign edge*lapse*p 2)

def chargedTransverseIndex (side edge : Fin 2) : Source.Index :=
  (⟨2*side.val+(1-edge.val),by omega⟩,edge)

def chargedTransverseRestriction (side edge : Fin 2) : DiracExteriorMatterCarrier :=
  (actualRestAmplitude 0*(spinScale:ℂ)) • embed (Pi.single (chargedTransverseIndex side edge) 1)

def chargedTransverseCoefficient (p : PhysicalMomentum) (side edge : Fin 2) : ℂ :=
  (chargedSideSign side:ℂ)*(lapse:ℂ)*((p 0:ℂ)+(chargedEdgeSign edge:ℂ)*Complex.I*(p 1:ℂ))

private theorem moving_entry (p : PhysicalMomentum) (row column : Source.Index) :
    sourceMovingFullHamiltonian p row column=
      if row.1.val/2=column.1.val/2 then
        (if row.1.val<2 then (-1:ℂ) else 1)*
          ChargedPreparation.SpatialSpectrum.sourceMatrix p
            ⟨2*(row.1.val%2)+row.2.val,by omega⟩
            ⟨2*(column.1.val%2)+column.2.val,by omega⟩ else 0 := by
  unfold sourceMovingFullHamiltonian
  rfl

private theorem actual_charged_matrix (p : PhysicalMomentum) (side edge : Fin 2) :
    sourceMovingFullHamiltonian p*ᵥ(Pi.single (sourceChargedBasisIndex side edge) 1)=
      (chargedEnergyDiagonal p side edge:ℂ) • Pi.single (sourceChargedBasisIndex side edge) 1+
      chargedTransverseCoefficient p side edge • Pi.single (chargedTransverseIndex side edge) 1 := by
  rw [Matrix.mulVec_single_one]
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [moving_entry,ChargedPreparation.SpatialSpectrum.sourceMatrix,
      sourceChargedBasisIndex,chargedTransverseIndex,chargedEnergyDiagonal,chargedSideSign,chargedEdgeSign,
      chargedTransverseCoefficient,Pi.add_apply,Pi.smul_apply,Pi.single_apply,Prod.mk.injEq,smul_eq_mul,
      Matrix.col_apply,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals ring
  all_goals simp

/-- The original Hamiltonian generates both the actual charged diagonal and its complete transverse leakage. -/
theorem actual_charged_hamiltonian (p : PhysicalMomentum) (side edge : Fin 2) :
    FullQuantum.hamiltonian actual 0 p (sourceChargedRestriction side edge)=
      (chargedEnergyDiagonal p side edge:ℂ) • sourceChargedRestriction side edge+
        chargedTransverseCoefficient p side edge • chargedTransverseRestriction side edge := by
  rw [sourceChargedRestriction_basis,map_smul,sourceMovingHamiltonian_original,actual_charged_matrix,
    map_add,map_smul,map_smul,chargedTransverseRestriction]
  module

/-- On the actual background axis the same charged leg is an exact pole at its generated energy. -/
theorem actual_charged_axis_hamiltonian (k : ℝ) (side edge : Fin 2) :
    FullQuantum.hamiltonian actual 0 (chargedAxisMomentum k) (sourceChargedRestriction side edge)=
      (chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ) • sourceChargedRestriction side edge := by
  rw [actual_charged_hamiltonian]
  simp [chargedTransverseCoefficient,chargedAxisMomentum]

/-- The positive actual charged leg has its original positive rest energy and linear axial continuation. -/
theorem actual_charged_positive_axis (k : ℝ) (nonnegative : 0≤k) :
    0<chargedEnergyDiagonal (chargedAxisMomentum k) 1 0 := by
  have hf:=ChargedPreparation.Dispersion.frequency_pos
  have hl:=lapse_pos
  norm_num [chargedEnergyDiagonal,chargedAxisMomentum,chargedSideSign,chargedEdgeSign,Matrix.cons_val_two]
  positivity

theorem actual_charged_axis_rest (side edge : Fin 2) :
    chargedEnergyDiagonal (chargedAxisMomentum 0) side edge=sourceActualChargedRestEnergy side := by
  simp [chargedEnergyDiagonal,chargedAxisMomentum,chargedSideSign,sourceActualChargedRestEnergy]

theorem actual_charged_axis_velocity (k : ℝ) (side edge : Fin 2) :
    HasDerivAt (fun x : ℝ=>chargedEnergyDiagonal (chargedAxisMomentum x) side edge)
      (chargedSideSign side*chargedEdgeSign edge*lapse) k := by
  simpa [chargedEnergyDiagonal,chargedAxisMomentum,Matrix.cons_val_two,mul_assoc] using
    (((hasDerivAt_id k).const_mul (chargedEdgeSign edge*lapse)).const_add (3*frequency)).const_mul
      (chargedSideSign side)

/-- The positive charged pole keeps its exact original resolvent at every axial momentum. -/
theorem actual_charged_axis_value (k : ℝ) (side edge : Fin 2) (energy damping : ℝ)
    (positive : 0<damping) :
    Retarded.value 0 (chargedAxisMomentum k) energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      (Complex.I/(Retarded.spectralParameter energy damping-
        (chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ))) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
  have nonzero : Retarded.spectralParameter energy damping-
      (chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ)≠0 := by
    intro zero
    have imag:=congrArg Complex.im zero
    simp [Retarded.spectralParameter] at imag
    exact positive.ne' imag
  have equation:=DFunLike.congr_fun (Retarded.value_kernel_right 0 (chargedAxisMomentum k) energy damping positive)
    (naturalCoordinates (sourceChargedRestriction side edge))
  rw [Retarded.kernel_original] at equation
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,operator_coordinates,
    actual_charged_axis_hamiltonian,map_smul,←sub_smul] at equation
  calc
    _=(Retarded.spectralParameter energy damping-(chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ))⁻¹ •
      ((Retarded.spectralParameter energy damping-(chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ)) •
        Retarded.value 0 (chargedAxisMomentum k) energy damping (naturalCoordinates (sourceChargedRestriction side edge))) := by
      rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    _=_ := by rw [equation,smul_smul];congr 1;ring

/-- The original C0 inverse flips the same independent charged input, without changing its charge label. -/
theorem actual_charged_axis_dirac (k : ℝ) (side edge : Fin 2) (energy damping : ℝ)
    (positive : 0<damping) :
    Retarded.diracValue 0 (chargedAxisMomentum k) energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      ((-(lapse:ℂ)*sourceRestSign side)/(Retarded.spectralParameter energy damping-
        (chargedEnergyDiagonal (chargedAxisMomentum k) (1-side) edge:ℂ))) •
        naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  rw [Retarded.diracValue_side 0 (chargedAxisMomentum k) energy damping positive,mul_apply_eq_comp,
    operator_coordinates,sourceActualChargedTemporalInverse,map_smul,map_smul,
    actual_charged_axis_value _ _ _ _ _ positive,smul_smul]
  congr 1
  field_simp
  simp
  all_goals ring

/-- The finite-momentum radial3frequency band is distinct from this same actual charged axial leg. -/
theorem actual_charged_axis_radial_gap (k : ℝ) (positive : 0<k) :
    ChargedPreparation.SpatialSpectrum.upperEnergy (chargedAxisMomentum k)<
      chargedEnergyDiagonal (chargedAxisMomentum k) 1 0 := by
  have hf:=ChargedPreparation.Dispersion.frequency_pos
  have hl:=lapse_pos
  have square:=ChargedPreparation.SpatialSpectrum.rate_sq (chargedAxisMomentum k)
  have nonnegative:=Real.sqrt_nonneg
    (frequency^2+lapse^2*ChargedPreparation.SpatialSpectrum.spatialSquare (chargedAxisMomentum k))
  change 0≤ChargedPreparation.SpatialSpectrum.rate (chargedAxisMomentum k) at nonnegative
  have square' : ChargedPreparation.SpatialSpectrum.rate (chargedAxisMomentum k)^2=
      frequency^2+lapse^2*k^2 := by
    simpa [ChargedPreparation.SpatialSpectrum.spatialSquare,chargedAxisMomentum,Fin.sum_univ_three] using square
  have product : 0<2*frequency*lapse*k := by positivity
  have bound : ChargedPreparation.SpatialSpectrum.rate (chargedAxisMomentum k)<frequency+lapse*k := by
    nlinarith [square',mul_pos hl positive]
  simpa [ChargedPreparation.SpatialSpectrum.upperEnergy,chargedEnergyDiagonal,chargedAxisMomentum,
    chargedSideSign,chargedEdgeSign,Matrix.cons_val_two] using (by linarith :
      2*frequency+ChargedPreparation.SpatialSpectrum.rate (chargedAxisMomentum k)<3*frequency+lapse*k)

/-- The generated axial velocity is constant, retaining the precise inertia-branch responsibility. -/
theorem actual_charged_axis_velocity_constant (k : ℝ) (side edge : Fin 2) :
    HasDerivAt (fun _ : ℝ=>chargedSideSign side*chargedEdgeSign edge*lapse) 0 k :=
  hasDerivAt_const k _

/-- The once-Dirac pole residue consumes the same actual charged maker at its generated axial pole. -/
theorem actual_charged_axis_residue_exact (k : ℝ) (side edge : Fin 2) (damping : ℝ)
    (positive : 0<damping) :
    (damping:ℂ) • Retarded.diracValue 0 (chargedAxisMomentum k)
      (chargedEnergyDiagonal (chargedAxisMomentum k) (1-side) edge) damping
      (naturalCoordinates (sourceChargedRestriction side edge))=
        (Complex.I*(lapse:ℂ)*sourceRestSign side) •
          naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  rw [actual_charged_axis_dirac _ _ _ _ _ positive,smul_smul]
  congr 1
  have nonzero : (damping:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [Retarded.spectralParameter,add_sub_cancel_left]
  field_simp
  simp

/-- The original complete moving spectrum selects the actual charged pole by energy, including every degeneracy. -/
theorem actual_charged_moving_support (k : ℝ) (side edge : Fin 2) (state : RestStateIndex)
    (different : sourceMovingPoleEnergy (chargedAxisMomentum k) state≠
      chargedEnergyDiagonal (chargedAxisMomentum k) side edge) :
    sourceChargedMovingCoefficient (chargedAxisMomentum k) side edge state=0 := by
  let p:=chargedAxisMomentum k
  let v : Source.Index→ℂ:=Pi.single (sourceChargedBasisIndex side edge) 1
  let u:=sourceMovingPoleValues p state
  have normalized : (spinScale:ℂ)⁻¹ • sourceRestStateValues (sourceChargedRestIndex side edge)=v := by
    rw [sourceChargedRestValues_basis,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr spinScale_pos.ne'),one_smul]
  have eigenV : sourceMovingFullHamiltonian p*ᵥv=
      (chargedEnergyDiagonal p side edge:ℂ) • v := by
    rw [actual_charged_matrix]
    simp [p,v,chargedTransverseCoefficient,chargedAxisMomentum]
  have eigenU:=sourceMovingFullHamiltonian_eigen p state
  have balance : dotProduct (star (sourceMovingFullHamiltonian p*ᵥu)) v=
      dotProduct (star u) (sourceMovingFullHamiltonian p*ᵥv) := by
    rw [Matrix.star_mulVec,sourceMovingFullHamiltonian_hermitian p,Matrix.dotProduct_mulVec]
  rw [eigenU,eigenV] at balance
  simp only [star_smul,Complex.star_def,Complex.conj_ofReal,smul_dotProduct,dotProduct_smul,smul_eq_mul] at balance
  have coefficient : sourceChargedMovingCoefficient p side edge state=dotProduct (star u) v := by
    unfold sourceChargedMovingCoefficient
    rw [normalized]
    rfl
  have equation : ((sourceMovingPoleEnergy p state:ℂ)-(chargedEnergyDiagonal p side edge:ℂ))*
      sourceChargedMovingCoefficient p side edge state=0 := by
    rw [coefficient]
    linear_combination balance
  have nonzero : (sourceMovingPoleEnergy p state:ℂ)-(chargedEnergyDiagonal p side edge:ℂ)≠0 :=
    sub_ne_zero.mpr (by exact_mod_cast different)
  exact (mul_eq_zero.mp equation).resolve_left nonzero

/-- The actual charged maker consumes all8 moving poles and automatically retains precisely its generated energy fiber. -/
theorem actual_charged_moving_energy_fiber (k : ℝ) (side edge : Fin 2) :
    sourceChargedRestriction side edge=∑state : RestStateIndex,
      if sourceMovingPoleEnergy (chargedAxisMomentum k) state=chargedEnergyDiagonal (chargedAxisMomentum k) side edge
      then sourceChargedMovingCoefficient (chargedAxisMomentum k) side edge state •
        actualMovingPolePreparation (chargedAxisMomentum k) state (embed (Source.vector 0)) else 0 := by
  rw [sourceChargedRestriction_moving (chargedAxisMomentum k)]
  apply Finset.sum_congr rfl
  intro state _
  by_cases same : sourceMovingPoleEnergy (chargedAxisMomentum k) state=chargedEnergyDiagonal (chargedAxisMomentum k) side edge
  · rw [if_pos same]
  · rw [if_neg same,actual_charged_moving_support k side edge state same,zero_smul]

end LowEnergy.GaussComposite.ActualChargedPoleDynamics
