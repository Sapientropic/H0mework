import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValueKernel
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesLorentz
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexLiterals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
noncomputable section
namespace LowEnergy.ActualCandidateVertexValues
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ActualCandidateVertexEntries ActualCandidateVertexLiterals MixedSpectatorCandidate
open MixedSpectatorContactVertices DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous PointwiseDiracSpinConnectionLift
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

open SU7MotherGaugeTheory StageNineLorentzConnectionVariation

private def backgroundSpin (mu : Fin 4) : DiracMatrix :=
  ![0, ((spinScale : ℂ)/2) • spinRotation 0,
    ((spinScale : ℂ)/2) • spinRotation 1, ((spinScale : ℂ)/2) • spinRotation 2] mu

private theorem actual_background_spin (mu : Fin 4) :
    diracSpinConnectionLift (actual.gravityConnection 0) mu = backgroundSpin mu := by
  rw [actual_gravityConnection]
  fin_cases mu
  · simp [diracSpinConnectionLift,homogeneousConnection,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,homogeneousContorsion,
      Fin.sum_univ_six,backgroundSpin]
  · exact homogeneousSpinLift spinScale 0
  · exact homogeneousSpinLift spinScale 1
  · exact homogeneousSpinLift spinScale 2

private def backgroundColor (amplitude : ℝ) (mu : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![0, ((amplitude : ℂ)/2) • colorRaw 1, ((amplitude : ℂ)/2) • colorRaw 0,
    ((amplitude : ℂ)/2) • (colorRaw 6-colorRaw 7)] mu

private theorem actual_background_color (amplitude : ℝ) (mu : Fin 4) :
    (gaugePotential amplitude mu).1.val = backgroundColor amplitude mu := by
  simp only [backgroundColor,sourceColorTable_original]
  fin_cases mu <;> ext c d <;> fin_cases c <;> fin_cases d <;>
    norm_num [gaugePotential,sourceColorP286Generator,p286LieBracket,suLieBracket,
      colorCartanGenerator,colorCartanRaw,colorMixingGenerator,colorMixingRaw,
      sourceColorTable,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

private theorem actual_background_weak (amplitude : ℝ) (mu : Fin 4) :
    (gaugePotential amplitude mu).2.1.val = 0 := by
  fin_cases mu <;> simp [gaugePotential,sourceColorP286Generator,p286LieBracket,suLieBracket]

private theorem actual_background_hyper (amplitude : ℝ) (mu : Fin 4) :
    (gaugePotential amplitude mu).2.2.val = 0 := by
  fin_cases mu <;> simp [gaugePotential,sourceColorP286Generator,p286LieBracket]

private theorem actual_adjugate (a nu mu b : Fin 4) :
    adjugateDerivative a nu mu b = lapse *
      (homogeneousCoframe lapse⁻¹ nu a * homogeneousCoframe lapse⁻¹ mu b -
       homogeneousCoframe lapse⁻¹ mu a * homogeneousCoframe lapse⁻¹ nu b) := by
  rw [adjugateDerivative,actual_coframe,homogeneousCoframe_det,
    homogeneousCoframe_inv lapse (ne_of_gt lapse_pos)]


private theorem sqrt30_square : (Real.sqrt 30 : ℂ)^2 = 30 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num)
private theorem sqrt2_square : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
private theorem sqrt15_square : (Real.sqrt 15 : ℂ)^2 = 15 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)

private theorem lapse_inv_value : (lapse : ℂ)⁻¹ = (5/18 : ℂ) * (Real.sqrt 30 : ℂ) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lapse_value]
  calc (3/25 : ℂ) * (Real.sqrt 30 : ℂ) * ((5/18 : ℂ) * (Real.sqrt 30 : ℂ)) =
      (1/30 : ℂ) * (Real.sqrt 30 : ℂ)^2 := by ring
    _ = 1 := by rw [sqrt30_square]; norm_num

private theorem sqrt30_factor : (Real.sqrt 30 : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt 15 : ℂ) := by
  have h : Real.sqrt 30 = Real.sqrt 2 * Real.sqrt 15 := by
    rw [←Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  rw [h]
  push_cast
  rfl


private def jetCurrent (mu b : Fin 4) (i j : NamedMode) : ℂ :=
  Complex.I * (
    (diracGammaZero * diracGamma b *
      diracSpinConnectionLift (actual.gravityConnection 0) mu) i.1 j.1 *
      (if i.2 = j.2 then 1 else 0) +
    (diracGammaZero * diracGamma b) i.1 j.1 *
      gaugeEntry (p286LieBlockEmbed (actual.gaugeConnection 0 mu)) i.2.1 i.2.2 j.2.1 j.2.2) +
  (if mu = 0 then (frequency : ℂ) *
    (diracGammaZero * diracGamma b * diracGammaFive) i.1 j.1 *
      (if i.2 = j.2 then 1 else 0) else 0)

private theorem actual_jet_current (mu b : Fin 4) (i j : NamedMode) :
    (∑ r : Fin 4, diracGammaZero i.1 r * jetEntry 0 mu b (r,i.2) j) =
      jetCurrent mu b i j := by
  rcases i with ⟨s,c,h⟩
  rcases j with ⟨t,d,k⟩
  unfold jetEntry connectionEntry jetCurrent
  simp only [Pi.zero_apply,zero_mul,zero_add,spin_entry_factor,internalEntry]
  simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  simp only [Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  by_cases hk : (c,h) = (d,k) <;> by_cases hm : mu = 0
  all_goals simp only [hk,hm,ite_true,ite_false,mul_one,mul_zero,add_zero,zero_add]
  all_goals simp only [Fin.sum_univ_four]
  all_goals ring

private theorem primitive_coframe (a : Fin 97) (h57 : 57 ≤ a.val) (h73 : a.val < 73)
    (i j : Support) :
    primitiveEntry 0 false a i j =
      ∑ mu : Fin 4, ∑ b : Fin 4,
        (adjugateDerivative ⟨(a.val-57)/4,by omega⟩
          ⟨(a.val-57)%4,Nat.mod_lt _ (by decide)⟩ mu b : ℂ) *
          jetCurrent mu b (supportNamed i) (supportNamed j) := by
  have h9 : ¬a.val < 9 := by omega
  have h57' : ¬a.val < 57 := by omega
  simp only [primitiveEntry,Bool.false_eq_true,ite_false,rawEntry,dif_neg h9,dif_neg h57',
    dif_pos h73,coframeEntry,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [←actual_jet_current,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [supportNamed]
  ring


private def adjugateFinite (a nu mu b : Fin 4) : ℝ :=
  if a.val = nu.val ∧ mu.val = b.val ∧ a.val ≠ mu.val then
    (if a.val = 0 ∨ mu.val = 0 then 1 else lapse)
  else if mu.val = a.val ∧ b.val = nu.val ∧ a.val ≠ nu.val then
    -(if a.val = 0 ∨ nu.val = 0 then 1 else lapse)
  else 0

private theorem actual_adjugate_finite (a nu mu b : Fin 4) :
    adjugateDerivative a nu mu b = adjugateFinite a nu mu b := by
  rw [actual_adjugate]
  have ln : lapse ≠ 0 := ne_of_gt lapse_pos
  fin_cases a <;> fin_cases nu <;> fin_cases mu <;> fin_cases b <;>
    norm_num [adjugateFinite,homogeneousCoframe,ln]

private theorem frequency_value : (frequency : ℂ) = (18/125 : ℂ) * (Real.sqrt 15 : ℂ) := by
  simp only [frequency,gaugeScale,spinScale,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_sub,Complex.ofReal_ofNat,lapse_value,sqrt30_factor]
  ring_nf
  rw [sqrt2_square]
  ring

private theorem lapse_spin_value : (lapse : ℂ) * (Real.sqrt 2 : ℂ) =
    (6/25 : ℂ) * (Real.sqrt 15 : ℂ) := by
  rw [lapse_value,sqrt30_factor]
  calc (3/25 : ℂ) * ((Real.sqrt 2 : ℂ) * (Real.sqrt 15 : ℂ)) * (Real.sqrt 2 : ℂ) =
      (3/25 : ℂ) * (Real.sqrt 2 : ℂ)^2 * (Real.sqrt 15 : ℂ) := by ring
    _ = (6/25 : ℂ) * (Real.sqrt 15 : ℂ) := by rw [sqrt2_square]; ring

private theorem lapse_spin_real : lapse * Real.sqrt 2 = (6/25 : ℝ) * Real.sqrt 15 := by
  apply Complex.ofReal_injective
  push_cast
  exact lapse_spin_value

private theorem lapse_real_value : lapse = (3/25 : ℝ) * Real.sqrt 30 := by
  apply Complex.ofReal_injective
  push_cast
  exact lapse_value

private theorem frequency_real_value : frequency = (18/125 : ℝ) * Real.sqrt 15 := by
  apply Complex.ofReal_injective
  push_cast
  exact frequency_value

private theorem sqrt30_real_factor : Real.sqrt 30 = Real.sqrt 2 * Real.sqrt 15 := by
  rw [←Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

private theorem support_explicit (i : Support) :
    supportNamed i = (i.1,i.2,(![0,0,1,1] : Fin 4 → Fin 2) i.1) := by
  rcases i with ⟨s,c⟩
  fin_cases s <;> rfl

private def row_57 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 8
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 9
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 10
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 11
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 10
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 9
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 8
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 11
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 12
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 13
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 14
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 15
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 14
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 13
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 12
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 15
  else 0

private theorem row_57_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 57 s t c d = row_57 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_57 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 57 (s,c) (t,d) = primalLiteral 57 s t c d := by
  rw [primitive_coframe 57 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 0 0 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_57_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_57]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_58 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else 0

private theorem row_58_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 58 s t c d = row_58 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_58 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 58 (s,c) (t,d) = primalLiteral 58 s t c d := by
  rw [primitive_coframe 58 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 0 1 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_58_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_58]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_59 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 17
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 17
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 17
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 18
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 18
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 18
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 17
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 17
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 17
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 18
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 18
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 18
  else 0

private theorem row_59_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 59 s t c d = row_59 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_59 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 59 (s,c) (t,d) = primalLiteral 59 s t c d := by
  rw [primitive_coframe 59 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 0 2 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_59_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_59]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_60 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 19
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 19
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 19
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 16
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 16
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 16
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 19
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 19
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 19
  else 0

private theorem row_60_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 60 s t c d = row_60 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_60 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 60 (s,c) (t,d) = primalLiteral 60 s t c d := by
  rw [primitive_coframe 60 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 0 3 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_60_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_60]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_61 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 20
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 21
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 20
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 21
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 21
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 20
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 21
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 20
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 20
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 21
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 20
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 21
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 21
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 20
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 21
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 20
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else 0

private theorem row_61_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 61 s t c d = row_61 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_61 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 61 (s,c) (t,d) = primalLiteral 61 s t c d := by
  rw [primitive_coframe 61 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 1 0 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_61_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_61]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_62 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 22
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 24
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 24
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 22
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 27
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 28
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 28
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 27
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else 0

private theorem row_62_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 62 s t c d = row_62 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_62 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 62 (s,c) (t,d) = primalLiteral 62 s t c d := by
  rw [primitive_coframe 62 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 1 1 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_62_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_62]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_63 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else 0

private theorem row_63_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 63 s t c d = row_63 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_63 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 63 (s,c) (t,d) = primalLiteral 63 s t c d := by
  rw [primitive_coframe 63 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 1 2 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_63_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_63]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_64 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 34
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 34
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 34
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 35
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 35
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 35
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 35
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 35
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 35
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 34
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 34
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 34
  else 0

private theorem row_64_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 64 s t c d = row_64 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_64 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 64 (s,c) (t,d) = primalLiteral 64 s t c d := by
  rw [primitive_coframe 64 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 1 3 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_64_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_64]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_65 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 36
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 37
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 38
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 37
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 37
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 39
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 36
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 39
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 38
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 39
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 36
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 37
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 38
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 37
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 37
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 39
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 36
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 39
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 38
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 39
  else 0

private theorem row_65_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 65 s t c d = row_65 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_65 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 65 (s,c) (t,d) = primalLiteral 65 s t c d := by
  rw [primitive_coframe 65 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 2 0 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_65_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_65]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_66 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else 0

private theorem row_66_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 66 s t c d = row_66 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_66 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 66 (s,c) (t,d) = primalLiteral 66 s t c d := by
  rw [primitive_coframe 66 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 2 1 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_66_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_66]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_67 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 22
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 24
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 25
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 24
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 25
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 22
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 27
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 28
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 23
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 28
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 23
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 27
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else 0

private theorem row_67_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 67 s t c d = row_67 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_67 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 67 (s,c) (t,d) = primalLiteral 67 s t c d := by
  rw [primitive_coframe 67 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 2 2 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_67_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_67]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_68 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 30
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 30
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 32
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 31
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 33
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 31
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 33
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 32
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else 0

private theorem row_68_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 68 s t c d = row_68 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_68 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 68 (s,c) (t,d) = primalLiteral 68 s t c d := by
  rw [primitive_coframe 68 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 2 3 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_68_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_68]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_69 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 40
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 41
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 42
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 43
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 44
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 40
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 41
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 21
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 42
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 43
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 44
  else 0

private theorem row_69_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 69 s t c d = row_69 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_69 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 69 (s,c) (t,d) = primalLiteral 69 s t c d := by
  rw [primitive_coframe 69 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 3 0 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_69_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_69]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_70 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 45
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 46
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 35
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 47
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 48
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 34
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 48
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 47
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 34
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 46
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 45
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 35
  else 0

private theorem row_70_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 70 s t c d = row_70 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_70 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 70 (s,c) (t,d) = primalLiteral 70 s t c d := by
  rw [primitive_coframe 70 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 3 1 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_70_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_70]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_71 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 49
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 50
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 50
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 49
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 33
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 51
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 52
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 52
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 51
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 30
  else 0

private theorem row_71_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 71 s t c d = row_71 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_71 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 71 (s,c) (t,d) = primalLiteral 71 s t c d := by
  rw [primitive_coframe 71 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 3 2 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_71_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_71]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

private def row_72 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 26
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 26
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 19
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 19
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 26
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 26
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 26
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 29
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 29
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 16
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 16
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 29
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 29
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 29
  else 0

private theorem row_72_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 72 s t c d = row_72 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_72 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 72 (s,c) (t,d) = primalLiteral 72 s t c d := by
  rw [primitive_coframe 72 (by decide) (by decide)]
  change (∑ mu : Fin 4,∑ b : Fin 4,
    (adjugateDerivative 3 3 mu b : ℂ) *
      jetCurrent mu b (supportNamed (s,c)) (supportNamed (t,d))) = _
  rw [row_72_original]
  simp only [actual_adjugate_finite,jetCurrent,actual_background_spin,
    actual_gaugeConnection,p286_entry,actual_background_color,actual_background_weak,
    actual_background_hyper,support_explicit]
  fin_cases s <;> fin_cases t <;>
    norm_num [adjugateFinite,backgroundSpin,backgroundColor,sourceColorTable_original,
      sourceColorTable,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_four,row_72]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try simp only [lapse_real_value,frequency_real_value,gaugeScale,spinScale,sqrt30_real_factor]
  all_goals push_cast
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ,
    Matrix.diagonal_apply,Fin.ext_iff,Fin.lt_def,Fin.le_def]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]
  all_goals repeat rw [lapse_value]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq,pow_succ]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_square,sqrt15_square,Complex.I_sq]

theorem actual_coframe_values (a : Fin 16) (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false ⟨a.val+57,by omega⟩ (s,c) (t,d) =
      primalLiteral ⟨a.val+57,by omega⟩ s t c d := by
  fin_cases a
  · exact primal_57 s t c d
  · exact primal_58 s t c d
  · exact primal_59 s t c d
  · exact primal_60 s t c d
  · exact primal_61 s t c d
  · exact primal_62 s t c d
  · exact primal_63 s t c d
  · exact primal_64 s t c d
  · exact primal_65 s t c d
  · exact primal_66 s t c d
  · exact primal_67 s t c d
  · exact primal_68 s t c d
  · exact primal_69 s t c d
  · exact primal_70 s t c d
  · exact primal_71 s t c d
  · exact primal_72 s t c d

end LowEnergy.ActualCandidateVertexValues
