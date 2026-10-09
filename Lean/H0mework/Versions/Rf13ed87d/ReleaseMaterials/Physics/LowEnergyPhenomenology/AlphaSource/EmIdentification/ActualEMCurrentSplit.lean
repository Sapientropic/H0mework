import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPreparedResidue

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCurrentSplit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource
open Stage10 StageNineHolonomicField CanonicalGradedSpatialSource
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open ActualEMCarrierOwn PhysicalEMGaugeRealization PhysicalEMFieldCurrent
open PreparationCoordinates PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalActualGaussChargeCurrent PreparationVacuumPhysicalQuantumLockedCharge
open DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open scoped Matrix BigOperators Topology
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] emInsertion sourceActualPreparedCurrent actualRestNativeComplexForcingCovector

private theorem em_slot (mu nu : Fin 4) (a : Fin 12) :
    emInsertion (gaugeSlot mu a) nu=
      if mu=nu then (rawCoordinates (p286CoordinateEquiv emDirection) a:ℂ) else 0 := by
  by_cases same : mu=nu
  · simp [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,gauge_gauge_slot,same]
  · simp [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,gauge_gauge_slot,same]

/-- This is the coordinate Gram of the literal three-slot injection, before any kinetic read. -/
theorem em_coordinate_gram :
    emInsertion.transpose*emInsertion=(3/4:ℂ) • (1:Matrix (Fin 4) (Fin 4) ℂ) := by
  ext mu nu
  change (emInsertion.transpose*ᵥ(fun j=>emInsertion j nu)) mu=_
  rw [em_projection_coordinates]
  simp only [em_slot,em_original_coordinates,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    Pi.single_apply,smul_eq_mul,Matrix.smul_apply,Matrix.one_apply]
  by_cases same : mu=nu <;> norm_num [same,Fin.ext_iff]

/-- Coordinate-dual injection fixed by the literal coordinate Gram. -/
def emCoordinateDual : Matrix (Fin 289) (Fin 4) ℂ := (4/3:ℂ) • emInsertion

theorem em_coordinate_dual : emInsertion.transpose*emCoordinateDual=1 := by
  rw [emCoordinateDual,Matrix.mul_smul,em_coordinate_gram,smul_smul]
  norm_num

def emCoordinateProjection : Matrix (Fin 289) (Fin 289) ℂ :=
  emCoordinateDual*emInsertion.transpose

theorem em_coordinate_projection_idem :
    emCoordinateProjection*emCoordinateProjection=emCoordinateProjection := by
  unfold emCoordinateProjection
  calc
    _=emCoordinateDual*(emInsertion.transpose*emCoordinateDual)*emInsertion.transpose := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [em_coordinate_dual,Matrix.mul_one]

/-- Original electromagnetic four-current; no assertion about the other 285 directions is made. -/
def emCurrent (f : Fin 289→ℂ) : Fin 4→ℂ := emInsertion.transpose*ᵥf

def emCoordinateCurrent (f : Fin 289→ℂ) : Fin 4→ℂ := (4/3:ℂ) • emCurrent f

def emCurrentForce (f : Fin 289→ℂ) : Fin 289→ℂ := emCoordinateDual*ᵥemCurrent f

def emCurrentResidual (f : Fin 289→ℂ) : Fin 289→ℂ := f-emCurrentForce f

theorem em_current_force_projection (f : Fin 289→ℂ) :
    emCurrentForce f=emCoordinateProjection*ᵥf := by
  simp only [emCurrentForce,emCurrent,emCoordinateProjection,Matrix.mulVec_mulVec]

theorem em_current_force_insertion (f : Fin 289→ℂ) :
    emCurrentForce f=emInsertion*ᵥemCoordinateCurrent f := by
  simp only [emCurrentForce,emCoordinateDual,emCoordinateCurrent,Matrix.smul_mulVec,Matrix.mulVec_smul]

theorem em_current_complete (f : Fin 289→ℂ) :
    f=emCurrentForce f+emCurrentResidual f := by
  unfold emCurrentResidual
  abel

theorem em_current_residual_projection (f : Fin 289→ℂ) :
    emCurrentResidual f=(1-emCoordinateProjection)*ᵥf := by
  rw [Matrix.sub_mulVec,Matrix.one_mulVec,←em_current_force_projection]
  rfl

theorem em_current_residual_zero (f : Fin 289→ℂ) :
    emInsertion.transpose*ᵥemCurrentResidual f=0 := by
  rw [emCurrentResidual,Matrix.mulVec_sub,emCurrentForce,Matrix.mulVec_mulVec,
    em_coordinate_dual,Matrix.one_mulVec]
  simp only [emCurrent,sub_self]

/-- The EM read of the complete rest force is the source's actual four-current. -/
theorem em_rest_current_generated (point : BasePoint) (left right : RestStateIndex) (mu : Fin 4) :
    emCurrent (actualRestNativeComplexForcingCovector point left right) mu=
      emForcingRead point left right mu := em_source_current point left right mu

/-- Charged and neutral temporal currents keep their source phase-momentum normalization. -/
theorem em_rest_current_temporal (side edge : Fin 2) :
    emCurrent (actualRestNativeComplexForcingCovector 0
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)) 0=
      (ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ) :=
  em_electron_source_unit side edge

/-- The four-current is also the exact finite source vertex of the same actual rest preparation. -/
theorem em_rest_current_vertex (point : BasePoint) (left right : RestStateIndex) (mu : Fin 4) :
    emCurrent (actualRestNativeComplexForcingCovector point left right) mu=
      (ActionNormalization.phaseMomentum:ℂ)*sourceRestGaugeVertexMixing mu emDirection left right := by
  rw [em_rest_current_generated,em_forcing_current]
  have density:=actualRestState_gaugeDensity_mixing mu emDirection point left right
  simpa only [sourceGaugeDensityAction_normal,LinearMap.smul_apply,map_smul,smul_eq_mul] using density

private def emRestSpin (side edge : Fin 2) : Fin 4 := ⟨2*side.val+edge.val,by omega⟩

private theorem em_rest_values_single (side edge : Fin 2) :
    sourceRestStateValues (sourceChargedRestIndex side edge)=
      (spinScale:ℂ) • Pi.single (emRestSpin side edge,edge) 1 := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceRestStateValues,sourceChargedRestIndex,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,ChargedPreparation.SpatialSpectrum.lowerValues,
      emRestSpin,Pi.single_apply,Fin.ext_iff]

private theorem em_gamma_diagonal (side edge : Fin 2) (mu : Fin 3) :
    -(diracGammaZero*diracGamma mu.succ) (emRestSpin side edge) (emRestSpin side edge)=
      if mu=2 then (sourceRestSign side:ℂ)*(sourceChargedPolarity edge:ℂ) else 0 := by
  fin_cases side <;> fin_cases edge <;> fin_cases mu <;>
    norm_num [emRestSpin,sourceRestSign,sourceChargedPolarity,Matrix.mul_apply,Fin.sum_univ_four,
      diracGammaZero,diracGamma,diracGammaOne,diracGammaTwo,diracGammaThree,Matrix.cons_val,Fin.ext_iff]

private theorem em_rest_vertex_single (side edge : Fin 2) (mu : Fin 4) :
    sourceRestGaugeVertexMixing mu emDirection
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)=
      (1/2:ℂ)*(star (spinScale:ℂ)*(spinScale:ℂ))*
        sourceGaugeVertexMatrix mu emDirection (emRestSpin side edge,edge) (emRestSpin side edge,edge) := by
  simp only [sourceRestGaugeVertexMixing,em_rest_values_single,Matrix.mulVec_smul,
    Matrix.mulVec_single_one,Pi.smul_apply]
  simp only [Pi.single_apply,apply_ite,ite_mul]
  have zeroStar : star (0:ℂ)=0 := star_zero ℂ
  simp only [Matrix.col_apply]
  ring_nf
  simp only [zeroStar,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem em_rest_spatial_vertex (side edge : Fin 2) (mu : Fin 3) :
    sourceRestGaugeVertexMixing mu.succ emDirection
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)=
      (if mu=2 then (lapse:ℂ)*(sourceRestSign side:ℂ)*(sourceChargedPolarity edge:ℂ) else 0)*
        sourceRestGaugeVertexMixing 0 emDirection
          (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge) := by
  have temporal : -(diracGammaZero*diracGamma 0) (emRestSpin side edge) (emRestSpin side edge)=1 := by
    rw [show diracGamma 0=diracGammaZero from rfl,diracGammaZero_sq]
    simp
  rw [em_rest_vertex_single,em_rest_vertex_single]
  simp only [sourceGaugeVertexMatrix,em_gamma_diagonal,temporal,sourceGaugeDensityWeight]
  by_cases last : mu=2
  · simp only [if_pos last,Fin.succ_ne_zero,if_false,if_true,one_mul]
    ring
  · simp only [if_neg last,Fin.succ_ne_zero,if_false,if_true,mul_zero,zero_mul]

/-- The actual bare diagonal preparation carries its generated longitudinal current as well as charge. -/
def emBareRestDirection (side : Fin 2) : Fin 4→ℂ :=
  ![1,0,0,(sourceRestSign side:ℂ)*(lapse:ℂ)]

/-- Source gamma/current calculation fixes the complete bare diagonal four-current. -/
theorem em_rest_diagonal_current (side edge : Fin 2) :
    emCurrent (actualRestNativeComplexForcingCovector 0
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge))=
      ((ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)) • emBareRestDirection side := by
  have charge:=em_rest_current_temporal side edge
  rw [em_rest_current_vertex] at charge
  funext mu
  induction mu using Fin.cases with
  | zero=>simpa [emBareRestDirection] using em_rest_current_temporal side edge
  | succ mu=>
      rw [em_rest_current_vertex,em_rest_spatial_vertex side edge mu]
      by_cases last : mu=2
      · subst mu
        change (ActionNormalization.phaseMomentum:ℂ)*
          ((lapse:ℂ)*(sourceRestSign side:ℂ)*(sourceChargedPolarity edge:ℂ)*
            sourceRestGaugeVertexMixing 0 emDirection
              (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge))=
          ((ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ))*
            ((sourceRestSign side:ℂ)*(lapse:ℂ))
        have polarity : (sourceChargedPolarity edge:ℂ)*(sourceActualPhaseCharge edge:ℂ)=
            (sourceActualPhaseCharge edge:ℂ) := by
          fin_cases edge <;> norm_num [sourceChargedPolarity,sourceActualPhaseCharge,Fin.ext_iff]
        calc
          _=(lapse:ℂ)*(sourceRestSign side:ℂ)*(sourceChargedPolarity edge:ℂ)*
              ((ActionNormalization.phaseMomentum:ℂ)*sourceRestGaugeVertexMixing 0 emDirection
                (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)) := by ring
          _=(lapse:ℂ)*(sourceRestSign side:ℂ)*(sourceChargedPolarity edge:ℂ)*
              ((ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)) := by rw [charge]
          _=(ActionNormalization.phaseMomentum:ℂ)*(lapse:ℂ)*(sourceRestSign side:ℂ)*
              ((sourceChargedPolarity edge:ℂ)*(sourceActualPhaseCharge edge:ℂ)) := by ring
          _=_ := by rw [polarity];ring
      · have zeroDirection : emBareRestDirection side mu.succ=0 := by
          fin_cases mu <;> simp [emBareRestDirection,Fin.ext_iff] at last ⊢
        simp only [if_neg last,mul_zero,zero_mul,Pi.smul_apply,zeroDirection,smul_zero]

/-- The prepared EM current retains all original sixty-four pair weights. -/
theorem em_prepared_current_all64 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) :
    emCurrent (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)=
      ∑a : RestStateIndex,∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 sL eL sR eR a b •
          emCurrent (PreparationVacuumFullPoleContinuation.returnedCurrentWindow q pL pR a b lambda T) := by
  simp only [sourceActualPreparedCurrent,emCurrent,Matrix.mulVec_sum,Matrix.mulVec_smul]

end LowEnergy.GaussComposite.ActualEMCurrentSplit
