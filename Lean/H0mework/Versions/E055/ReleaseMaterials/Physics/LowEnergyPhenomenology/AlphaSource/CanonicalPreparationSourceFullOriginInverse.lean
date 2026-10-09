import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceWholeOriginCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullOriginResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin
open scoped Matrix BigOperators Topology

namespace Heavy
def flag (i : Fin 289) : Bool := ([11,12,13,14,17,18,23,24,25,26,29,30,35,36,37,38,41,42,47,48,49,50,53,54,68,71,74,77,78,81,84,87] : List (Fin 289)).contains i
def projection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix flag
def originTerms : List SourceTerm:=selectedRows flag (columnTerms flag (PreparationVacuumMixedPrincipal.originTerms activeTerms))
private def inverseTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(3375/94994:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-15625/94994:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(15625/94994:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(115/1188:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/1188:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(25/162:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/1188:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/162:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(10655725/46167084:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(2382625/11541771:ℚ)⟩⟩)]
private def inverseTermsCodes : List ℕ := [
  38280,39121,39194,41760,42469,42542,45240,46022,46093,48720,49370,49441,59163,62643,80044,80201,80357,80706,
  80778,83524,83659,83837,84054,84126,87004,87163,87271,87680,87752,90484,90617,90751,91028,91100,100929,104409,
  121675,121804,121985,122202,122274,125129,125284,125443,125792,125864,128633,128764,128897,129174,129246,132091,132244,132355,
  132764,132836,142689,146169,163303,163459,163564,163976,164048,166783,166913,167044,167324,167396,170213,170371,170524,170876,
  170948,173693,173825,174004,174224,174296,184449,187929,235994,236118,236250,236432,236650,236723,246373,246548,246678,246812,
  247090,247163,256801,256926,257058,257240,257459,257530,267182,267356,267486,267620,267899,267970,270662,270786,270944,271100,
  271450,271523,281041,281216,281372,281480,281890,281963,291469,291594,291752,291908,292259,292330,301850,302024,302180,302288,
  302699,302770]
def inverseTerms : List SourceTerm := decodeTerms inverseTermsAtoms inverseTermsCodes

def inverse : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix inverseTerms 0

theorem origin_generated : sourceMatrix originTerms 0=projection*activeKernel 0*projection:=by
  rw [originTerms,selectedRows_generated,columnTerms_value,originTerms_generated]
  simp only [mul_assoc]
  rfl
private theorem inverse_left_certificate :
    fastNormalizeTerms (productTerms inverseTerms originTerms++negativeTerms (projectionTerms flag))=[]:=by decide +kernel

theorem inverse_left : inverse*sourceMatrix originTerms 0=projection:=by
  have h:=normalization_equal _ _ inverse_left_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,inverse,projection] using h
private theorem inverse_left_support_certificate :
    fastNormalizeTerms (productTerms (projectionTerms flag) inverseTerms++negativeTerms inverseTerms)=[]:=by decide +kernel
private theorem inverse_right_support_certificate :
    fastNormalizeTerms (productTerms inverseTerms (projectionTerms flag)++negativeTerms inverseTerms)=[]:=by decide +kernel

theorem inverse_left_support : projection*inverse=inverse:=by
  have h:=normalization_equal _ _ inverse_left_support_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,inverse,projection] using h

theorem inverse_right_support : inverse*projection=inverse:=by
  have h:=normalization_equal _ _ inverse_right_support_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,inverse,projection] using h
end Heavy


def componentInverseTerms : Fin 3→List SourceTerm:=
  ![PreparationVacuumMixedEffective.complementInverseTerms,PreparationVacuumWholeOrigin.Dual.complementInverseTerms,Heavy.inverseTerms]
def componentOriginTerms : Fin 3→List SourceTerm:=
  ![PreparationVacuumMixedEffective.complementOriginTerms,PreparationVacuumWholeOrigin.Dual.complementOriginTerms,Heavy.originTerms]
def componentFlag : Fin 3→Fin 289→Bool:=
  ![PreparationVacuumMixedEffective.complementFlag,PreparationVacuumWholeOrigin.Dual.complementFlag,Heavy.flag]
def componentInverse (i : Fin 3) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix (componentInverseTerms i) 0
def componentOrigin (i : Fin 3) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix (componentOriginTerms i) 0
def componentProjection (i : Fin 3) : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix (componentFlag i)

theorem component_inverse_left (i : Fin 3) : componentInverse i*componentOrigin i=componentProjection i:=by
  fin_cases i
  · change PreparationVacuumMixedEffective.complementInverse*sourceMatrix PreparationVacuumMixedEffective.complementOriginTerms 0=
      PreparationVacuumMixedEffective.complementProjection
    rw [PreparationVacuumMixedEffective.complementOrigin_generated]
    exact PreparationVacuumMixedEffective.complementInverse_left
  · change PreparationVacuumWholeOrigin.Dual.complementInverse*sourceMatrix PreparationVacuumWholeOrigin.Dual.complementOriginTerms 0=
      PreparationVacuumWholeOrigin.Dual.complementProjection
    rw [PreparationVacuumWholeOrigin.Dual.complementOrigin_generated]
    exact PreparationVacuumWholeOrigin.Dual.complementInverse_left
  · exact Heavy.inverse_left

theorem component_inverse_left_support (i : Fin 3) : componentProjection i*componentInverse i=componentInverse i:=by
  fin_cases i
  · exact PreparationVacuumMixedEffective.complementInverse_left_support
  · exact PreparationVacuumWholeOrigin.Dual.complementInverse_left_support
  · exact Heavy.inverse_left_support

theorem component_inverse_right_support (i : Fin 3) : componentInverse i*componentProjection i=componentInverse i:=by
  fin_cases i
  · exact PreparationVacuumMixedEffective.complementInverse_right_support
  · exact PreparationVacuumWholeOrigin.Dual.complementInverse_right_support
  · exact Heavy.inverse_right_support

private theorem component_cross_certificate : ∀i j : Fin 3,i≠j→
    fastNormalizeTerms (productTerms (componentInverseTerms i) (componentOriginTerms j))=[]:=by decide +kernel

theorem component_inverse_cross (i j : Fin 3) (different : i≠j) : componentInverse i*componentOrigin j=0:=by
  have h:=normalization_equal (productTerms (componentInverseTerms i) (componentOriginTerms j)) []
    (by simpa only [negativeTerms,List.map_nil,List.append_nil] using component_cross_certificate i j different) (0:Fin 4→ℂ)
  simpa only [componentInverse,componentOrigin,productTerms_value,sourceMatrix_nil] using h

def fullComplementFlag (i : Fin 289) : Bool:=activeFlag i && !([83,85,89,95,101] : List (Fin 289)).contains i
def fullComplementProjection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix fullComplementFlag
def fullOriginTerms : List SourceTerm:=selectedRows fullComplementFlag
  (columnTerms fullComplementFlag (PreparationVacuumMixedPrincipal.originTerms activeTerms))
def fullOrigin : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix fullOriginTerms 0
def fullInverse : Matrix (Fin 289) (Fin 289) ℂ:=∑i : Fin 3,componentInverse i

private theorem full_projection_certificate :
    fastNormalizeTerms ((projectionTerms (componentFlag 0)++projectionTerms (componentFlag 1)++projectionTerms (componentFlag 2))++
      negativeTerms (projectionTerms fullComplementFlag))=[]:=by decide +kernel

theorem fullProjection_sum : fullComplementProjection=∑i : Fin 3,componentProjection i:=by
  have h:=normalization_equal _ _ full_projection_certificate (0:Fin 4→ℂ)
  simpa only [sourceMatrix_append,projectionTerms_value,fullComplementProjection,componentProjection,Fin.sum_univ_three] using h.symm

private theorem full_projection_piece_certificate : ∀i : Fin 3,
    fastNormalizeTerms (productTerms (projectionTerms fullComplementFlag) (projectionTerms (componentFlag i))++
      negativeTerms (projectionTerms (componentFlag i)))=[]:=by decide +kernel

theorem fullProjection_piece (i : Fin 3) : fullComplementProjection*componentProjection i=componentProjection i:=by
  have h:=normalization_equal _ _ (full_projection_piece_certificate i) (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,fullComplementProjection,componentProjection] using h

theorem piece_fullProjection (i : Fin 3) : componentProjection i*fullComplementProjection=componentProjection i:=by
  have h:=congrArg Matrix.transpose (fullProjection_piece i)
  simpa only [Matrix.transpose_mul,componentProjection,fullComplementProjection,projectionMatrix,Matrix.diagonal_transpose] using h

private theorem full_origin_split_certificate :
    fastNormalizeTerms ((componentOriginTerms 0++componentOriginTerms 1++componentOriginTerms 2)++negativeTerms fullOriginTerms)=[]:=by decide +kernel

theorem fullOrigin_sum : fullOrigin=∑i : Fin 3,componentOrigin i:=by
  have h:=normalization_equal _ _ full_origin_split_certificate (0:Fin 4→ℂ)
  simpa only [sourceMatrix_append,fullOrigin,componentOrigin,Fin.sum_univ_three] using h.symm

theorem fullOrigin_generated : fullOrigin=fullComplementProjection*activeKernel 0*fullComplementProjection:=by
  unfold fullOrigin fullOriginTerms
  rw [selectedRows_generated,columnTerms_value,originTerms_generated]
  simp only [mul_assoc]
  rfl

theorem fullInverse_left : fullInverse*fullOrigin=fullComplementProjection:=by
  rw [fullInverse,fullOrigin_sum,fullProjection_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · exact component_inverse_left i
  · intro j _ different
    exact component_inverse_cross i j (Ne.symm different)
  · simp

theorem fullInverse_left_support : fullComplementProjection*fullInverse=fullInverse:=by
  unfold fullInverse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=fullComplementProjection*(componentProjection i*componentInverse i):=by rw [component_inverse_left_support]
    _=componentInverse i:=by rw [←mul_assoc,fullProjection_piece,component_inverse_left_support]

theorem fullInverse_right_support : fullInverse*fullComplementProjection=fullInverse:=by
  unfold fullInverse
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=(componentInverse i*componentProjection i)*fullComplementProjection:=by rw [component_inverse_right_support]
    _=componentInverse i:=by rw [mul_assoc,piece_fullProjection,component_inverse_right_support]

theorem fullProjection_square : fullComplementProjection*fullComplementProjection=fullComplementProjection:=by
  unfold fullComplementProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

def complementKernel (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullComplementProjection*activeKernel p*fullComplementProjection+(1-fullComplementProjection)
def originInverse : Matrix (Fin 289) (Fin 289) ℂ:=fullInverse+(1-fullComplementProjection)

theorem originInverse_left : originInverse*complementKernel 0=1:=by
  have pair : fullInverse*(fullComplementProjection*activeKernel 0*fullComplementProjection)=fullComplementProjection:=by
    rw [←fullOrigin_generated];exact fullInverse_left
  have support : fullComplementProjection*(fullComplementProjection*activeKernel 0*fullComplementProjection)=
      fullComplementProjection*activeKernel 0*fullComplementProjection:=by simp only [←mul_assoc,fullProjection_square]
  unfold originInverse complementKernel
  calc
    _=fullInverse*(fullComplementProjection*activeKernel 0*fullComplementProjection)+fullInverse-
        fullInverse*fullComplementProjection+(fullComplementProjection*activeKernel 0*fullComplementProjection)-
        fullComplementProjection*(fullComplementProjection*activeKernel 0*fullComplementProjection)+
        1-fullComplementProjection-fullComplementProjection+fullComplementProjection*fullComplementProjection:=by noncomm_ring
    _=1:=by rw [pair,support,fullInverse_right_support,fullProjection_square];noncomm_ring

theorem originInverse_right : complementKernel 0*originInverse=1:=mul_eq_one_comm.mp originInverse_left

theorem origin_determinant : (complementKernel 0).det≠0:=by
  have h:=congrArg Matrix.det originInverse_right
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro zero
  rw [zero,zero_mul] at h
  exact zero_ne_one h

end LowEnergy.PreparationVacuumFullOriginResponse
