import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeFieldCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMasslessStaticPair

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeStaticCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumStaticPoleResponse PreparationVacuumPhysicalConstraint114
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumLowerClassical PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic PreparationPhysicalStaticSpatialCouplingReturn
open ActualCompositeFieldCurrent ActualMasslessStaticPair ActualWholeStatic
open scoped Matrix BigOperators Topology
attribute [local irreducible] fullNativeOrigin ActualCompositeFieldCurrent.compositeCurrent ActualCompositeFieldCurrent.compositeDetector wholeStaticLimit

private theorem origin_held_read (v : Fin 289→ℂ)
    (held : ∀i : Fin 289,PreparationVacuumPhysicalConstraint114.sourceHeldUnsupported i→v i=0) :
    fullNativeOrigin.transpose*ᵥv=
      Pi.single 0 ((3/10:ℂ)*rootTwo*(v 21-v 34))+
      Pi.single 1 ((3/10:ℂ)*rootTwo*(v 21-v 34)) := by
  let flag : Fin 289→Bool:=fun (i : Fin 289)=>
    !(decide (((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i))
  let terms : List SourceTerm:=[
    ⟨0,21,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨1,21,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨0,34,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨1,34,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩]
  have selected : columnTerms flag (reflectedTerms fullNativeOriginTerms)=terms := by decide +kernel
  have supported : projectionMatrix flag*ᵥv=v := by
    funext i
    simp only [projectionMatrix,Matrix.mulVec_diagonal]
    by_cases h : PreparationVacuumPhysicalConstraint114.sourceHeldUnsupported i
    · have support:=held i h
      simp only [support,mul_zero]
    · have outside : ¬(((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i) := h
      have on : flag i=true := by
        have value : decide (((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i)=false :=
          decide_eq_false_iff_not.mpr outside
        dsimp only [flag]
        rw [value]
        rfl
      simp only [on,if_true,one_mul]
  have projected : fullNativeOrigin.transpose*projectionMatrix flag=sourceMatrix terms 0 := by
    calc
      _=sourceMatrix (reflectedTerms fullNativeOriginTerms) 0*projectionMatrix flag := by
        rw [reflectedTerms_value,neg_zero,←fullNativeOrigin_generated]
      _=sourceMatrix (columnTerms flag (reflectedTerms fullNativeOriginTerms)) 0 :=
        (columnTerms_value _ _ _).symm
      _=_ := by rw [selected]
  rw [←supported,Matrix.mulVec_mulVec,projected,supported]
  norm_num [terms,sourceMatrix,SourceTerm.matrix,Matrix.add_mulVec,Matrix.zero_mulVec,
    Matrix.single_mulVec,Powers.value,coefficientValue]
  ext i
  simp only [Pi.single_apply,Function.update_apply,Pi.zero_apply,Pi.add_apply]
  split_ifs  <;> ring

private theorem static_inverse_pair (w : ℂ) :
    staticInverse*ᵥ(Pi.single 0 w+Pi.single 1 w)=
      Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*w)+
      Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*w) := by
  norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  congr 1

/-- Original action support applies to arbitrary actual N3 endpoints, without a gauge-only premise. -/
theorem composite_current_held (p : PhysicalMomentum) (left right : CompositeLeg)
    (i : Fin 289) (held : sourceHeldUnsupported i) : ActualCompositeFieldCurrent.compositeCurrent p left right i=0 := by
  rw [ActualCompositeFieldCurrent.compositeCurrent,sourceHeld_rawForm_zero i held,neg_zero]

def compositeMasslessWeight (p : PhysicalMomentum) (left right : CompositeLeg) : ℂ :=
  (3/10:ℂ)*rootTwo*(ActualCompositeFieldCurrent.compositeCurrent p left right 21-ActualCompositeFieldCurrent.compositeCurrent p left right 34)

/-- All289 original origin rows are consumed; unsupported matter/auxiliary action slots vanish by the source law. -/
theorem composite_origin_read (p : PhysicalMomentum) (left right : CompositeLeg) :
    fullNativeOrigin.transpose*ᵥActualCompositeFieldCurrent.compositeCurrent p left right=
      Pi.single 0 (compositeMasslessWeight p left right)+Pi.single 1 (compositeMasslessWeight p left right) := by
  exact origin_held_read _ (composite_current_held p left right)

/-- The surviving spatial coupling remains a concrete original action integral on the complete N3 responses. -/
theorem composite_weight_action (p : PhysicalMomentum) (left right : CompositeLeg) :
    compositeMasslessWeight p left right=
      (3/10:ℂ)*rootTwo*(-rawForm (PreparationVacuumActionFieldLift.fieldUnit 21) p (compositeUnitLeg left) (compositeUnitLeg right) 0+
        rawForm (PreparationVacuumActionFieldLift.fieldUnit 34) p (compositeUnitLeg left) (compositeUnitLeg right) 0) := by
  simp only [compositeMasslessWeight,ActualCompositeFieldCurrent.compositeCurrent,sub_neg_eq_add]

/-- One original static inverse acts between the independently normalized complete N3 current endpoints. -/
theorem composite_static_pair (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) (staticResidue (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))=
      -actualStaticPairSeed*compositeMasslessWeight pd dL dR*compositeMasslessWeight ps sL sR := by
  have transpose_pair (M : Matrix (Fin 289) (Fin 289) ℂ) (u v : Fin 289→ℂ) :
      dotProduct u (M*ᵥv)=dotProduct (M.transpose*ᵥu) v := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold staticResidue
  rw [transpose_pair,composite_origin_read,composite_origin_read,
    static_inverse_pair]
  simp only [dotProduct_add,dotProduct_single,Pi.add_apply,Pi.single_apply]
  norm_num [Fin.ext_iff]
  unfold actualStaticPairSeed
  ring


/-- The whole-field Green coefficient uses the new N3 source current and one original hc detector. -/
theorem composite_full_green_coefficient (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    dotProduct (ActualCompositeFieldCurrent.compositeDetector branch pd dL dR) (wholeStaticLimit*ᵥActualCompositeFieldCurrent.compositeCurrent ps sL sR)=
      actualStaticPairSeed*compositeMasslessWeight pd dL dR*compositeMasslessWeight ps sL sR/
        (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)) := by
  rw [composite_whole_coefficient,ActualCompositeFieldCurrent.compositeDetector,smul_dotProduct,composite_static_pair]
  simp only [smul_eq_mul,div_eq_mul_inv]
  ring

/-- The actual fullN3 event consumes the complete uniform Green limit with its generated origin coefficient. -/
theorem composite_full_green_uniform (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃radius : ℝ, 0<radius ∧ ∀r : staticDomain, r.val<radius→
      ∀n : PhysicalMomentum, ∀unit : spatialSquare n=1,
        ‖(r.val:ℂ)^2*dotProduct (ActualCompositeFieldCurrent.compositeDetector branch pd dL dR)
          (sourceGreen (sourceSpatialStaticRegularPoint n unit r)*ᵥActualCompositeFieldCurrent.compositeCurrent ps sL sR)-
            actualStaticPairSeed*compositeMasslessWeight pd dL dR*compositeMasslessWeight ps sL sR/
              (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))‖≤epsilon := by
  simpa only [composite_full_green_coefficient] using
    composite_whole_green_uniform branch pd ps dL dR sL sR epsilon positive

end LowEnergy.GaussComposite.ActualCompositeStaticCurrent
