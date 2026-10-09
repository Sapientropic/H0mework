import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraPairData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualBraDualPair
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValueKernel
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualContactDualImaginaryCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra ActualContactDualImaginary MixedSpectatorDual24Data MixedSpectatorDual24Exchange
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix
attribute [local irreducible] dualCoefficient dualAxialValue axialSourceMap pairPoint

private theorem sum_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑a,∑b,∑i,∑j,f a b i j) = ∑i,∑j,∑a,∑b,f a b i j := by
  calc
    _ = ∑a,∑i,∑j,∑b,f a b i j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

/-- The two original source maps contract against the same actual bra pair
before reading the paid independent-dual inverse. -/
theorem actual_dual_bra_exchange (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,((-1/2 : ℂ)*dualCoefficient Complex.I 0 a b)*pairPoint dual a b) =
      ∑i : Fin 24,∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue i j)*
        (∑a : Fin 97,∑b : Fin 97,axialSourceMap i a*pairPoint dual a b*axialSourceMap j b) := by
  simp only [actual_dual_coefficient_point,Finset.mul_sum,Finset.sum_mul]
  rw [sum_four]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring


theorem actual_dual_source_pair (i j : Fin 24) (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,axialSourceMap i a*pairPoint dual a b*axialSourceMap j b) =
      dualSourceSign i*dualSourceSign j*
        dualPairForm (dualSourceClass i) (dualSourceClass j) := by
  simp_rw [actual_dual_source_form]
  calc
    _ = dualSourceSign i*dualSourceSign j *
        (∑a : Fin 97,∑b : Fin 97,
          dualSourceForm (dualSourceClass i) a*pairPoint dual a b*
            dualSourceForm (dualSourceClass j) b) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [actual_dual_form_pair]

private theorem axial_point_0_0 (b : Fin 24) (hb : b.val = 0) : dualAxialValue 0 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (0 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_0_4 (b : Fin 24) (hb : b.val = 4) : dualAxialValue 0 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (4 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_0_6 (b : Fin 24) (hb : b.val = 6) : dualAxialValue 0 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (6 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_0_10 (b : Fin 24) (hb : b.val = 10) : dualAxialValue 0 b =
    (((-159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (10 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_4_0 (b : Fin 24) (hb : b.val = 0) : dualAxialValue 4 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (0 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_4_4 (b : Fin 24) (hb : b.val = 4) : dualAxialValue 4 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (4 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_4_6 (b : Fin 24) (hb : b.val = 6) : dualAxialValue 4 b =
    (((-159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (6 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_4_10 (b : Fin 24) (hb : b.val = 10) : dualAxialValue 4 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (10 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_6_0 (b : Fin 24) (hb : b.val = 0) : dualAxialValue 6 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (0 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_6_4 (b : Fin 24) (hb : b.val = 4) : dualAxialValue 6 b =
    (((-159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (4 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_6_6 (b : Fin 24) (hb : b.val = 6) : dualAxialValue 6 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (6 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_6_10 (b : Fin 24) (hb : b.val = 10) : dualAxialValue 6 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (10 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_10_0 (b : Fin 24) (hb : b.val = 0) : dualAxialValue 10 b =
    (((-159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (0 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_10_4 (b : Fin 24) (hb : b.val = 4) : dualAxialValue 10 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (4 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_10_6 (b : Fin 24) (hb : b.val = 6) : dualAxialValue 10 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (6 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_10_10 (b : Fin 24) (hb : b.val = 10) : dualAxialValue 10 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (10 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_12_12 (b : Fin 24) (hb : b.val = 12) : dualAxialValue 12 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (12 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_12_16 (b : Fin 24) (hb : b.val = 16) : dualAxialValue 12 b =
    (((28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (16 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_12_18 (b : Fin 24) (hb : b.val = 18) : dualAxialValue 12 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (18 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_12_22 (b : Fin 24) (hb : b.val = 22) : dualAxialValue 12 b =
    (((159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (22 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_13_13 (b : Fin 24) (hb : b.val = 13) : dualAxialValue 13 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (13 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_13_15 (b : Fin 24) (hb : b.val = 15) : dualAxialValue 13 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (15 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_13_19 (b : Fin 24) (hb : b.val = 19) : dualAxialValue 13 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (19 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_13_21 (b : Fin 24) (hb : b.val = 21) : dualAxialValue 13 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (21 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_15_13 (b : Fin 24) (hb : b.val = 13) : dualAxialValue 15 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (13 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_15_21 (b : Fin 24) (hb : b.val = 21) : dualAxialValue 15 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (21 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_16_12 (b : Fin 24) (hb : b.val = 12) : dualAxialValue 16 b =
    (((28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (12 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_16_16 (b : Fin 24) (hb : b.val = 16) : dualAxialValue 16 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (16 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_16_18 (b : Fin 24) (hb : b.val = 18) : dualAxialValue 16 b =
    (((159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (18 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_16_22 (b : Fin 24) (hb : b.val = 22) : dualAxialValue 16 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (22 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_18_12 (b : Fin 24) (hb : b.val = 12) : dualAxialValue 18 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (12 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_18_16 (b : Fin 24) (hb : b.val = 16) : dualAxialValue 18 b =
    (((159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (16 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_18_18 (b : Fin 24) (hb : b.val = 18) : dualAxialValue 18 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (18 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_18_22 (b : Fin 24) (hb : b.val = 22) : dualAxialValue 18 b =
    (((28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (22 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_19_13 (b : Fin 24) (hb : b.val = 13) : dualAxialValue 19 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (13 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_19_21 (b : Fin 24) (hb : b.val = 21) : dualAxialValue 19 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (21 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_21_13 (b : Fin 24) (hb : b.val = 13) : dualAxialValue 21 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (13 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_21_15 (b : Fin 24) (hb : b.val = 15) : dualAxialValue 21 b =
    (((27/100) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (15 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_21_19 (b : Fin 24) (hb : b.val = 19) : dualAxialValue 21 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (19 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_21_21 (b : Fin 24) (hb : b.val = 21) : dualAxialValue 21 b =
    (((-51/250) : ℂ)/((-869/625) : ℂ))/(lapse : ℂ) := by
  have he : b = (21 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_22_12 (b : Fin 24) (hb : b.val = 12) : dualAxialValue 22 b =
    (((159027/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (12 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_22_16 (b : Fin 24) (hb : b.val = 16) : dualAxialValue 22 b =
    (((-28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (16 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_22_18 (b : Fin 24) (hb : b.val = 18) : dualAxialValue 22 b =
    (((28677/250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (18 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem axial_point_22_22 (b : Fin 24) (hb : b.val = 22) : dualAxialValue 22 b =
    (((852489/1250000) : ℂ)/((755161/390625) : ℂ))/(lapse : ℂ) := by
  have he : b = (22 : Fin 24) := Fin.ext hb
  subst b
  unfold dualAxialValue
  rfl

private theorem outer_row_0 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 0 j)*
      (dualSourceSign 0*dualSourceSign j*dualPairForm (dualSourceClass 0) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_0_0,axial_point_0_4,axial_point_0_6,axial_point_0_10]
  all_goals norm_num
  all_goals ring

private theorem outer_row_1 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 1 j)*
      (dualSourceSign 1*dualSourceSign j*dualPairForm (dualSourceClass 1) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_2 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 2 j)*
      (dualSourceSign 2*dualSourceSign j*dualPairForm (dualSourceClass 2) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_3 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 3 j)*
      (dualSourceSign 3*dualSourceSign j*dualPairForm (dualSourceClass 3) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_4 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 4 j)*
      (dualSourceSign 4*dualSourceSign j*dualPairForm (dualSourceClass 4) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_4_0,axial_point_4_4,axial_point_4_6,axial_point_4_10]
  all_goals norm_num
  all_goals ring

private theorem outer_row_5 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 5 j)*
      (dualSourceSign 5*dualSourceSign j*dualPairForm (dualSourceClass 5) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_6 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 6 j)*
      (dualSourceSign 6*dualSourceSign j*dualPairForm (dualSourceClass 6) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_6_0,axial_point_6_4,axial_point_6_6,axial_point_6_10]
  all_goals norm_num
  all_goals ring

private theorem outer_row_7 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 7 j)*
      (dualSourceSign 7*dualSourceSign j*dualPairForm (dualSourceClass 7) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_8 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 8 j)*
      (dualSourceSign 8*dualSourceSign j*dualPairForm (dualSourceClass 8) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_9 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 9 j)*
      (dualSourceSign 9*dualSourceSign j*dualPairForm (dualSourceClass 9) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_10 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 10 j)*
      (dualSourceSign 10*dualSourceSign j*dualPairForm (dualSourceClass 10) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_10_0,axial_point_10_4,axial_point_10_6,axial_point_10_10]
  all_goals norm_num
  all_goals ring

private theorem outer_row_11 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 11 j)*
      (dualSourceSign 11*dualSourceSign j*dualPairForm (dualSourceClass 11) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_12 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 12 j)*
      (dualSourceSign 12*dualSourceSign j*dualPairForm (dualSourceClass 12) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_12_12,axial_point_12_16,axial_point_12_18,axial_point_12_22]
  all_goals norm_num
  all_goals ring

private theorem outer_row_13 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 13 j)*
      (dualSourceSign 13*dualSourceSign j*dualPairForm (dualSourceClass 13) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_13_13,axial_point_13_15,axial_point_13_19,axial_point_13_21]
  all_goals norm_num
  all_goals ring

private theorem outer_row_14 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 14 j)*
      (dualSourceSign 14*dualSourceSign j*dualPairForm (dualSourceClass 14) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_15 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 15 j)*
      (dualSourceSign 15*dualSourceSign j*dualPairForm (dualSourceClass 15) (dualSourceClass j))) =
      (243/7900 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_15_13,axial_point_15_21]
  all_goals norm_num
  all_goals ring

private theorem outer_row_16 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 16 j)*
      (dualSourceSign 16*dualSourceSign j*dualPairForm (dualSourceClass 16) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_16_12,axial_point_16_16,axial_point_16_18,axial_point_16_22]
  all_goals norm_num
  all_goals ring

private theorem outer_row_17 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 17 j)*
      (dualSourceSign 17*dualSourceSign j*dualPairForm (dualSourceClass 17) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_18 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 18 j)*
      (dualSourceSign 18*dualSourceSign j*dualPairForm (dualSourceClass 18) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_18_12,axial_point_18_16,axial_point_18_18,axial_point_18_22]
  all_goals norm_num
  all_goals ring

private theorem outer_row_19 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 19 j)*
      (dualSourceSign 19*dualSourceSign j*dualPairForm (dualSourceClass 19) (dualSourceClass j))) =
      (243/7900 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_19_13,axial_point_19_21]
  all_goals norm_num
  all_goals ring

private theorem outer_row_20 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 20 j)*
      (dualSourceSign 20*dualSourceSign j*dualPairForm (dualSourceClass 20) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem outer_row_21 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 21 j)*
      (dualSourceSign 21*dualSourceSign j*dualPairForm (dualSourceClass 21) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_21_13,axial_point_21_15,axial_point_21_19,axial_point_21_21]
  all_goals norm_num
  all_goals ring

private theorem outer_row_22 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 22 j)*
      (dualSourceSign 22*dualSourceSign j*dualPairForm (dualSourceClass 22) (dualSourceClass j))) =
      (-729/15800 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]
  all_goals norm_num [axial_point_22_12,axial_point_22_16,axial_point_22_18,axial_point_22_22]
  all_goals norm_num
  all_goals ring

private theorem outer_row_23 :
    (∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue 23 j)*
      (dualSourceSign 23*dualSourceSign j*dualPairForm (dualSourceClass 23) (dualSourceClass j))) =
      (0 : ℂ)/(lapse : ℂ) := by
  norm_num [Fin.sum_univ_succ,dualSourceSign,dualSourceClass,dualPairForm]

private theorem actual_dual_outer_value :
    (∑i : Fin 24,∑j : Fin 24,((-1/2 : ℂ)*dualAxialValue i j)*
      (dualSourceSign i*dualSourceSign j*dualPairForm (dualSourceClass i) (dualSourceClass j))) =
      (-243/790 : ℂ)/(lapse : ℂ) := by
  let f : Fin 24 → ℂ := fun i => ∑j : Fin 24,
    ((-1/2 : ℂ)*dualAxialValue i j)*
      (dualSourceSign i*dualSourceSign j*dualPairForm (dualSourceClass i) (dualSourceClass j))
  change (∑i : Fin 24,f i) = _
  have hf : f = ![(-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (243/7900 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (243/7900 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-729/15800 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ)] := by
    funext i
    fin_cases i
    · exact outer_row_0
    · exact outer_row_1
    · exact outer_row_2
    · exact outer_row_3
    · exact outer_row_4
    · exact outer_row_5
    · exact outer_row_6
    · exact outer_row_7
    · exact outer_row_8
    · exact outer_row_9
    · exact outer_row_10
    · exact outer_row_11
    · exact outer_row_12
    · exact outer_row_13
    · exact outer_row_14
    · exact outer_row_15
    · exact outer_row_16
    · exact outer_row_17
    · exact outer_row_18
    · exact outer_row_19
    · exact outer_row_20
    · exact outer_row_21
    · exact outer_row_22
    · exact outer_row_23
  rw [hf]
  norm_num [Fin.sum_univ_succ]
  ring

private theorem lapse_dual_value :
    (-243/790 : ℂ)/(lapse : ℂ) = (-27/316 : ℂ)*(Real.sqrt 30 : ℂ) := by
  have hs : (Real.sqrt 30 : ℂ)^2 = 30 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num)
  rw [ActualCandidateVertexValues.lapse_value]
  have hi : ((3/25 : ℂ)*(Real.sqrt 30 : ℂ))⁻¹ =
      (5/18 : ℂ)*(Real.sqrt 30 : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (1/30 : ℂ)*(Real.sqrt 30 : ℂ)^2 := by ring
      _ = 1 := by rw [hs]; norm_num
  rw [div_eq_mul_inv,hi]
  ring

/-- The original independent-dual inverse at the fixed regular point,
contracted with the source candidate's actual bra-pair values. -/
theorem actual_dual_bra_value (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*dualCoefficient Complex.I 0 a b)*pairPoint dual a b) =
      (-27/316 : ℂ)*(Real.sqrt 30 : ℂ) := by
  rw [actual_dual_bra_exchange]
  simp_rw [actual_dual_source_pair]
  rw [actual_dual_outer_value,lapse_dual_value]

end LowEnergy.ActualBraContactDualContraction
