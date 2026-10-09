import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Majorant
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Endpoint
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Exchange
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericHeat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Integrability

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceExponential SourceCoulomb
open GaussianPair Laplace.Axis
open MeasureTheory Set
noncomputable section

theorem sPairRate_envelope (a b : Term) :
    sPairRate (pairEnvelope a b).1 (pairEnvelope a b).2 = (pairRateM a b : ℝ) := by
  unfold sPairRate
  rw [← Rat.cast_add, pairEnvelope_rate]

theorem sPairRate_envelope_pos (a b : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    0 < sPairRate (pairEnvelope a b).1 (pairEnvelope a b).2 := by
  rw [sPairRate_envelope]
  exact_mod_cast pairRateM_pos a b ha hb

theorem sHeatInner_nonneg (left right nextLeft nextRight : Term) (t : ℝ)
    (hc1 : 0 ≤ sPairCoefficient left right)
    (hc2 : 0 ≤ sPairCoefficient nextLeft nextRight)
    (hr1 : 0 < sPairRate left right) (hr2 : 0 < sPairRate nextLeft nextRight) :
    0 ≤ sHeatInner left right nextLeft nextRight t := by
  unfold sHeatInner
  have hD : 0 < sPairRate left right * sPairRate nextLeft nextRight +
      (sPairRate left right + sPairRate nextLeft nextRight)*t^2 :=
    add_pos_of_pos_of_nonneg (mul_pos hr1 hr2)
      (mul_nonneg (add_pos hr1 hr2).le (sq_nonneg t))
  apply mul_nonneg
  · apply mul_nonneg (mul_nonneg hc1 hc2)
    exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (div_nonneg Real.pi_nonneg (Real.sqrt_nonneg _))
      (Real.exp_pos _).le

theorem sHeatInner_le_outer (a b c d : Term) (t : ℝ)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent)
    (hc : 0 < c.exponent) (hd : 0 < d.exponent) (_ht : 0 < t) :
    sHeatInner (pairEnvelope a b).1 (pairEnvelope a b).2
        (pairEnvelope c d).1 (pairEnvelope c d).2 t ≤
      (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
        Real.pi^3 *
        outerMajorant ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))
          ((pairRateM a b : ℝ) + (pairRateM c d : ℝ)) t := by
  have hρ : 0 < sPairRate (pairEnvelope a b).1 (pairEnvelope a b).2 :=
    sPairRate_envelope_pos a b ha hb
  have hρ' : 0 < sPairRate (pairEnvelope c d).1 (pairEnvelope c d).2 :=
    sPairRate_envelope_pos c d hc hd
  set ρ : ℝ := sPairRate (pairEnvelope a b).1 (pairEnvelope a b).2 with hρd
  set ρ' : ℝ := sPairRate (pairEnvelope c d).1 (pairEnvelope c d).2 with hρ'd
  unfold sHeatInner
  rw [← hρd, ← hρ'd]
  set D : ℝ := ρ*ρ' + (ρ+ρ')*t^2 with hDd
  have hD : 0 < D := hDd ▸ add_pos_of_pos_of_nonneg (mul_pos hρ hρ')
    (mul_nonneg (add_pos hρ hρ').le (sq_nonneg t))
  have hρe : ρ = (pairRateM a b : ℝ) := sPairRate_envelope a b
  have hρ'e : ρ' = (pairRateM c d : ℝ) := sPairRate_envelope c d
  have hcoef1 := sPairCoefficient_envelope_nonneg a b ha hb
  have hcoef2 := sPairCoefficient_envelope_nonneg c d hc hd
  have hcoef1le := sPairCoefficient_envelope_le a b ha hb
  have hcoef2le := sPairCoefficient_envelope_le c d hc hd
  have hκ1 : (0:ℝ) ≤ pairKappa a b := by
    exact_mod_cast pairKappa_nonneg a b ha.le hb.le
  have hκ2 : (0:ℝ) ≤ pairKappa c d := by
    exact_mod_cast pairKappa_nonneg c d hc.le hd.le
  have hΔ : ∀ axis : Fin 3, 0 ≤ ρ*ρ'*t^2/D *
      (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
        sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2 :=
    fun axis => mul_nonneg (div_nonneg (mul_nonneg (mul_pos hρ hρ').le
      (sq_nonneg t)) hD.le) (sq_nonneg _)
  have hexp1 : ∀ axis : Fin 3,
      Real.exp (-(ρ*ρ'*t^2/D *
        (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
          sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2)) ≤ 1 :=
    fun axis => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hΔ axis))
  have hprode : ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
        (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
          sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2)) ≤ 1 := by
    calc ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
            (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
              sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2))
        ≤ ∏ _ : Fin 3, (1:ℝ) :=
          Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
            (fun axis _ => hexp1 axis)
      _ = 1 := Finset.prod_const_one
  have hprode_nn : (0:ℝ) ≤ ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
        (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
          sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2)) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hDnonneg : (0:ℝ) ≤ Real.pi/Real.sqrt D :=
    div_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  have hp3 : (Real.pi/Real.sqrt D)^3 = Real.pi^3/(D*Real.sqrt D) := by
    have h3 : (Real.sqrt D)^3 = D*Real.sqrt D := by
      rw [pow_succ, Real.sq_sqrt hD.le]
    rw [div_pow, h3]
  have hprod : ∏ axis : Fin 3, (Real.pi/Real.sqrt D *
        Real.exp (-(ρ*ρ'*t^2/D *
          (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
            sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2))) =
      (Real.pi/Real.sqrt D)^3 *
        ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
          (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
            sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hprod]
  calc sPairCoefficient (pairEnvelope a b).1 (pairEnvelope a b).2 *
        sPairCoefficient (pairEnvelope c d).1 (pairEnvelope c d).2 *
        (2 / Real.sqrt Real.pi) * ((Real.pi/Real.sqrt D)^3 *
          ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
            (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
              sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2)))
      ≤ (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
          ((Real.pi/Real.sqrt D)^3 *
            ∏ axis : Fin 3, Real.exp (-(ρ*ρ'*t^2/D *
              (sPairCentre (pairEnvelope a b).1 (pairEnvelope a b).2 axis -
                sPairCentre (pairEnvelope c d).1 (pairEnvelope c d).2 axis)^2))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hcoef1le hcoef2le hcoef2 hκ1)
            (div_nonneg (by norm_num) (Real.sqrt_nonneg _)))
          (mul_nonneg (pow_nonneg hDnonneg 3) hprode_nn)
    _ ≤ (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
          ((Real.pi/Real.sqrt D)^3) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hκ1 hκ2)
          (div_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        exact le_trans (mul_le_mul_of_nonneg_left hprode
          (pow_nonneg hDnonneg 3)) (le_of_eq (mul_one _))
    _ = (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
          Real.pi^3 *
          (1/(D*Real.sqrt D)) := by
        rw [hp3]
        ring
    _ = (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
          Real.pi^3 *
          outerMajorant ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))
            ((pairRateM a b : ℝ) + (pairRateM c d : ℝ)) t := by
        unfold outerMajorant
        rw [← hρe, ← hρ'e, ← hDd]

theorem envelope_primitive_bound (a b c d : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent)
    (hc : 0 < c.exponent) (hd : 0 < d.exponent) :
    GaussianPair.primitiveInteraction (pairEnvelope a b) (pairEnvelope c d) ≤
      (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
        Real.pi^3 /
        ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
          Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ))) := by
  obtain ⟨hL1, hR1⟩ := pairEnvelope_exponents_positive a b ha hb
  obtain ⟨hL2, hR2⟩ := pairEnvelope_exponents_positive c d hc hd
  obtain ⟨hsL1, hsR1⟩ := pairEnvelope_sPowers a b
  obtain ⟨hsL2, hsR2⟩ := pairEnvelope_sPowers c d
  have hρ : (0:ℝ) < (pairRateM a b : ℝ) := by
    exact_mod_cast pairRateM_pos a b ha hb
  have hρ' : (0:ℝ) < (pairRateM c d : ℝ) := by
    exact_mod_cast pairRateM_pos c d hc hd
  have hcc : (0:ℝ) < (pairRateM a b : ℝ)*(pairRateM c d : ℝ) := mul_pos hρ hρ'
  have hss : (0:ℝ) < (pairRateM a b : ℝ)+(pairRateM c d : ℝ) := add_pos hρ hρ'
  have hswap : GaussianPair.primitiveInteraction
        ((pairEnvelope a b).1, (pairEnvelope a b).2)
        ((pairEnvelope c d).1, (pairEnvelope c d).2) =
      Laplace.primitiveHeatInteraction ((pairEnvelope a b).1, (pairEnvelope a b).2)
        ((pairEnvelope c d).1, (pairEnvelope c d).2) :=
    Laplace.primitive_interaction_heat_swapped _ _ _ _ hL1 hR1 hL2 hR2
  have houter := s_primitive_outer (pairEnvelope a b).1 (pairEnvelope a b).2
    (pairEnvelope c d).1 (pairEnvelope c d).2 hsL1 hsR1 hsL2 hsR2
    hL1 hR1 hL2 hR2
  have hmono : (∫ t in Ioi (0:ℝ), sHeatInner (pairEnvelope a b).1
        (pairEnvelope a b).2 (pairEnvelope c d).1 (pairEnvelope c d).2 t) ≤
      ∫ t in Ioi (0:ℝ), ((pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
        (2 / Real.sqrt Real.pi) * Real.pi^3) *
        outerMajorant ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))
          ((pairRateM a b : ℝ) + (pairRateM c d : ℝ)) t := by
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
        sHeatInner_nonneg _ _ _ _ t
          (sPairCoefficient_envelope_nonneg a b ha hb)
          (sPairCoefficient_envelope_nonneg c d hc hd)
          (sPairRate_envelope_pos a b ha hb)
          (sPairRate_envelope_pos c d hc hd))
    · exact (outerMajorant_integrable _ _ hcc hss).const_mul _
    · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
        sHeatInner_le_outer a b c d t ha hb hc hd ht)
  rw [integral_const_mul, outerMajorant_integral _ _ hcc hss] at hmono
  have h1 : ((pairEnvelope a b).1, (pairEnvelope a b).2) = pairEnvelope a b := rfl
  have h2 : ((pairEnvelope c d).1, (pairEnvelope c d).2) = pairEnvelope c d := rfl
  rw [← h1, ← h2, hswap, houter]
  exact hmono.trans (le_of_eq (mul_one_div _ _))

theorem sqrt_two_mul_sqrt_le (ρ ρ' : ℝ) (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    Real.sqrt 2 * Real.sqrt (Real.sqrt (ρ*ρ')) ≤ Real.sqrt (ρ + ρ') := by
  have ham : 2 * Real.sqrt (ρ*ρ') ≤ ρ + ρ' := by
    have e : (√ρ - √ρ')^2 = ρ + ρ' - 2*Real.sqrt (ρ*ρ') := by
      rw [sub_sq, Real.sq_sqrt hρ.le, Real.sq_sqrt hρ'.le, Real.sqrt_mul hρ.le]
      ring
    have hnn : (√ρ - √ρ')^2 ≥ 0 := sq_nonneg _
    linarith
  calc Real.sqrt 2 * Real.sqrt (Real.sqrt (ρ*ρ'))
      = Real.sqrt (2 * Real.sqrt (ρ*ρ')) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ Real.sqrt (ρ + ρ') := Real.sqrt_le_sqrt ham

theorem pairPhi_pow4_mul_le (a b c d : Term)
    (hρM : (0:ℚ) < pairRateM a b) (hρM' : (0:ℚ) < pairRateM c d) :
    ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))^4 ≤
      (pairRateM a b : ℝ) * (pairRateM c d : ℝ) := by
  have h1 : (pairPhi a b : ℝ)^4 ≤ (pairRateM a b : ℝ) := by
    have h := pairPhi_pow_le a b hρM
    calc (pairPhi a b : ℝ)^4 = ((pairPhi a b^4 : ℚ) : ℝ) := by
          rw [Rat.cast_pow]
      _ ≤ _ := by exact_mod_cast h
  have h2 : (pairPhi c d : ℝ)^4 ≤ (pairRateM c d : ℝ) := by
    have h := pairPhi_pow_le c d hρM'
    calc (pairPhi c d : ℝ)^4 = ((pairPhi c d^4 : ℚ) : ℝ) := by
          rw [Rat.cast_pow]
      _ ≤ _ := by exact_mod_cast h
  have hφ'nn : (0:ℝ) ≤ (pairPhi c d : ℝ)^4 :=
    pow_nonneg (by exact_mod_cast pairPhi_nonneg c d) 4
  have hρR : (0:ℝ) ≤ (pairRateM a b : ℝ) := by exact_mod_cast hρM.le
  rw [mul_pow]
  exact mul_le_mul h1 h2 hφ'nn hρR

theorem phi_mul_le_sqrt_sqrt (a b c d : Term)
    (hρM : (0:ℚ) < pairRateM a b) (hρM' : (0:ℚ) < pairRateM c d)
    (_hφ : (0:ℚ) < pairPhi a b) (_hφ' : (0:ℚ) < pairPhi c d) :
    (pairPhi a b : ℝ) * (pairPhi c d : ℝ) ≤
      Real.sqrt (Real.sqrt ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))) := by
  have hρR : (0:ℝ) < (pairRateM a b : ℝ) := by exact_mod_cast hρM
  have hρ'R : (0:ℝ) < (pairRateM c d : ℝ) := by exact_mod_cast hρM'
  have hsq : ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))^2 ≤
      Real.sqrt ((pairRateM a b : ℝ) * (pairRateM c d : ℝ)) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0)
      (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (mul_nonneg hρR.le hρ'R.le)]
    calc (((pairPhi a b : ℝ) * (pairPhi c d : ℝ))^2)^2
        = ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))^4 := by ring
      _ ≤ (pairRateM a b : ℝ) * (pairRateM c d : ℝ) :=
          pairPhi_pow4_mul_le a b c d hρM hρM'
  apply le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0)
    (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  exact hsq

theorem pairC0_sq_bound :
    Real.sqrt 2 * Real.pi^2 * Real.sqrt Real.pi ≤ (pairC0 : ℝ)^2 := by
  have hc0 : (0:ℝ) ≤ (pairC0 : ℝ) := by
    have h : (0:ℚ) < pairC0 := by unfold pairC0; norm_num
    exact_mod_cast h.le
  apply le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) (pow_nonneg hc0 2)
  have hexp : (Real.sqrt 2 * Real.pi^2 * Real.sqrt Real.pi)^2 =
      2 * Real.pi^5 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sq_sqrt Real.pi_nonneg]
    ring
  have hc4 : ((pairC0 : ℝ)^2)^2 = (pairC0 : ℝ)^4 := by ring
  rw [hexp, hc4]
  have hpi : Real.pi^5 < (3.1416:ℝ)^5 :=
    pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_nonneg (by norm_num : (5:ℕ) ≠ 0)
  have h498 : (2:ℝ) * (3.1416:ℝ)^5 ≤ ((498/100 : ℚ) : ℝ)^4 := by norm_num
  have hc : (pairC0 : ℝ) = ((498/100 : ℚ) : ℝ) := by unfold pairC0; rfl
  rw [hc]
  linarith

theorem twoPiSq_sqrtPhi_mul_le (a b c d : Term)
    (hρM : (0:ℚ) < pairRateM a b) (hρM' : (0:ℚ) < pairRateM c d)
    (hφ : (0:ℚ) < pairPhi a b) (hφ' : (0:ℚ) < pairPhi c d) :
    2 * Real.pi^2 * Real.sqrt Real.pi *
      ((pairPhi a b : ℝ) * (pairPhi c d : ℝ)) ≤
      (pairC0 : ℝ)^2 *
        Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ)) := by
  have hρR : (0:ℝ) < (pairRateM a b : ℝ) := by exact_mod_cast hρM
  have hρ'R : (0:ℝ) < (pairRateM c d : ℝ) := by exact_mod_cast hρM'
  have hφφ' := phi_mul_le_sqrt_sqrt a b c d hρM hρM' hφ hφ'
  have hbridge := sqrt_two_mul_sqrt_le ((pairRateM a b : ℝ))
    ((pairRateM c d : ℝ)) hρR hρ'R
  have h2pi : (0:ℝ) ≤ 2 * Real.pi^2 * Real.sqrt Real.pi := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = (2:ℝ) := Real.mul_self_sqrt (by norm_num)
  have hc0 : (0:ℝ) ≤ (pairC0 : ℝ) := by
    have h : (0:ℚ) < pairC0 := by unfold pairC0; norm_num
    exact_mod_cast h.le
  calc 2 * Real.pi^2 * Real.sqrt Real.pi *
        ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))
      ≤ 2 * Real.pi^2 * Real.sqrt Real.pi *
        Real.sqrt (Real.sqrt ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))) :=
        mul_le_mul_of_nonneg_left hφφ' h2pi
    _ = (Real.sqrt 2 * Real.pi^2 * Real.sqrt Real.pi) *
        (Real.sqrt 2 * Real.sqrt (Real.sqrt
          ((pairRateM a b : ℝ) * (pairRateM c d : ℝ)))) := by
        conv_lhs => rw [hs2.symm]
        ring
    _ ≤ (pairC0 : ℝ)^2 * Real.sqrt ((pairRateM a b : ℝ) +
          (pairRateM c d : ℝ)) :=
        mul_le_mul pairC0_sq_bound hbridge (by positivity)
          (pow_nonneg hc0 2)

theorem kappaPi_bound_le (a b c d : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent)
    (hc : 0 < c.exponent) (hd : 0 < d.exponent)
    (hrate1 : (1/64 : ℚ) ≤ pairRateM a b) (hrate2 : (1/64 : ℚ) ≤ pairRateM c d) :
    (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
      Real.pi^3 /
      ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
        Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ))) ≤
    (pairTau a b : ℝ) * (pairTau c d : ℝ) := by
  have hρM : (0:ℚ) < pairRateM a b := pairRateM_pos a b ha hb
  have hρM' : (0:ℚ) < pairRateM c d := pairRateM_pos c d hc hd
  have hφ : (0:ℚ) < pairPhi a b := pairPhi_pos a b hrate1
  have hφ' : (0:ℚ) < pairPhi c d := pairPhi_pos c d hrate2
  have hρR : (0:ℝ) < (pairRateM a b : ℝ) := by exact_mod_cast hρM
  have hρ'R : (0:ℝ) < (pairRateM c d : ℝ) := by exact_mod_cast hρM'
  have hφR : (0:ℝ) < (pairPhi a b : ℝ) := by exact_mod_cast hφ
  have hφ'R : (0:ℝ) < (pairPhi c d : ℝ) := by exact_mod_cast hφ'
  have hκ1 : (0:ℝ) ≤ (pairKappa a b : ℝ) := by
    exact_mod_cast pairKappa_nonneg a b ha.le hb.le
  have hκ2 : (0:ℝ) ≤ (pairKappa c d : ℝ) := by
    exact_mod_cast pairKappa_nonneg c d hc.le hd.le
  have hS : (0:ℝ) < Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ)) :=
    Real.sqrt_pos.mpr (add_pos hρR hρ'R)
  have hsep := twoPiSq_sqrtPhi_mul_le a b c d hρM hρM' hφ hφ'
  have hτ1 := pairTau_ge a b hρM hφ
  have hτ2 := pairTau_ge c d hρM' hφ'
  have hτ1nn : (0:ℝ) ≤ (pairTau a b : ℝ) := by
    exact_mod_cast pairTau_nonneg a b ha.le hb.le hρM hφ
  have hτ2nn : (0:ℝ) ≤ (pairTau c d : ℝ) := by
    exact_mod_cast pairTau_nonneg c d hc.le hd.le hρM' hφ'
  have hc0 : (0:ℝ) ≤ (pairC0 : ℝ) := by
    have h : (0:ℚ) < pairC0 := by unfold pairC0; norm_num
    exact_mod_cast h.le
  have hπpos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hfac : (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
        Real.pi^3 =
      (pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
        (2 * Real.pi^2 * Real.sqrt Real.pi) := by
    have h : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
      Real.mul_self_sqrt Real.pi_nonneg
    have h23 : (2 / Real.sqrt Real.pi) * Real.pi^3 =
        2 * Real.pi^2 * Real.sqrt Real.pi := by
      calc (2 / Real.sqrt Real.pi) * Real.pi^3
          = 2 * Real.pi^3 / Real.sqrt Real.pi := by ring
        _ = (2 * Real.pi^3) * Real.sqrt Real.pi /
              (Real.sqrt Real.pi * Real.sqrt Real.pi) :=
            (mul_div_mul_right _ _ hπpos.ne').symm
        _ = 2 * Real.pi^3 * Real.sqrt Real.pi / Real.pi := by rw [h]
        _ = 2 * Real.pi^2 * Real.sqrt Real.pi := by
            rw [div_eq_iff Real.pi_pos.ne']
            ring
    calc (pairKappa a b : ℝ) * (pairKappa c d : ℝ) * (2 / Real.sqrt Real.pi) *
          Real.pi^3
        = (pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
          ((2 / Real.sqrt Real.pi) * Real.pi^3) := by ring
      _ = _ := by rw [h23]
  rw [hfac]
  have hbound : (pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
        (2 * Real.pi^2 * Real.sqrt Real.pi) /
        ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
          Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ))) ≤
      ((pairC0 : ℝ)^2 * ((pairKappa a b : ℝ) * (pairKappa c d : ℝ))) /
        ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
          ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))) := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos hρR hρ'R) hS)
      (mul_pos (mul_pos hρR hρ'R) (mul_pos hφR hφ'R))]
    calc (pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
          (2 * Real.pi^2 * Real.sqrt Real.pi) *
          ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
            ((pairPhi a b : ℝ) * (pairPhi c d : ℝ)))
        = ((pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
            ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))) *
          (2 * Real.pi^2 * Real.sqrt Real.pi *
            ((pairPhi a b : ℝ) * (pairPhi c d : ℝ))) := by ring
      _ ≤ ((pairKappa a b : ℝ) * (pairKappa c d : ℝ) *
            ((pairRateM a b : ℝ) * (pairRateM c d : ℝ))) *
          ((pairC0 : ℝ)^2 *
            Real.sqrt ((pairRateM a b : ℝ) + (pairRateM c d : ℝ))) :=
          mul_le_mul_of_nonneg_left hsep
            (mul_nonneg (mul_nonneg hκ1 hκ2) (mul_pos hρR hρ'R).le)
      _ = _ := by ring
  refine hbound.trans ?_
  calc ((pairC0 : ℝ)^2 * ((pairKappa a b : ℝ) * (pairKappa c d : ℝ))) /
        ((pairRateM a b : ℝ) * (pairRateM c d : ℝ) *
          ((pairPhi a b : ℝ) * (pairPhi c d : ℝ)))
      = ((pairC0 : ℝ) * (pairKappa a b : ℝ) /
          ((pairRateM a b : ℝ) * (pairPhi a b : ℝ))) *
        ((pairC0 : ℝ) * (pairKappa c d : ℝ) /
          ((pairRateM c d : ℝ) * (pairPhi c d : ℝ))) := by
        rw [div_mul_div_comm]
        congr 1
        · ring
        · ring
    _ ≤ (pairTau a b : ℝ) * (pairTau c d : ℝ) := by
        apply mul_le_mul
        · exact hτ1
        · exact hτ2
        · exact div_nonneg (mul_nonneg hc0 hκ2) (mul_nonneg hρ'R.le hφ'R.le)
        · exact hτ1nn

theorem primitiveInteraction_abs_le (a b c d : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent)
    (hc : 0 < c.exponent) (hd : 0 < d.exponent)
    (hrate1 : (1/64 : ℚ) ≤ pairRateM a b) (hrate2 : (1/64 : ℚ) ≤ pairRateM c d) :
    |GaussianPair.primitiveInteraction (a, b) (c, d)| ≤
      (pairTau a b : ℝ) * (pairTau c d : ℝ) := by
  obtain ⟨hL1, hR1⟩ := pairEnvelope_exponents_positive a b ha hb
  obtain ⟨hL2, hR2⟩ := pairEnvelope_exponents_positive c d hc hd
  have hkernel_nn : ∀ z : Point × Point, 0 ≤ kernel (z.2 - z.1) := fun z =>
    inv_nonneg.mpr (distance_nonnegative _)
  have hdom : Integrable (fun z : Point × Point =>
      pairShape (pairEnvelope a b).1 (pairEnvelope a b).2 z.1 *
      pairShape (pairEnvelope c d).1 (pairEnvelope c d).2 z.2 *
      kernel (z.2 - z.1)) :=
    pair_kernel_integrable _ _ _ _ hL1 hR1 hL2 hR2
  have habs : |GaussianPair.primitiveInteraction (a, b) (c, d)| ≤
      GaussianPair.primitiveInteraction (pairEnvelope a b) (pairEnvelope c d) := by
    calc |GaussianPair.primitiveInteraction (a, b) (c, d)|
        = ‖GaussianPair.primitiveInteraction (a, b) (c, d)‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ ∫ z : Point × Point,
          ‖pairShape a b z.1 * pairShape c d z.2 * kernel (z.2 - z.1)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ z : Point × Point,
          |pairShape a b z.1| * |pairShape c d z.2| * kernel (z.2 - z.1) := by
          congr 1
          funext z
          rw [Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (hkernel_nn z)]
      _ ≤ ∫ z : Point × Point,
          pairShape (pairEnvelope a b).1 (pairEnvelope a b).2 z.1 *
          pairShape (pairEnvelope c d).1 (pairEnvelope c d).2 z.2 *
          kernel (z.2 - z.1) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ (fun z => mul_nonneg
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hkernel_nn z))
          · exact hdom
          · exact ae_of_all _ (fun z =>
              mul_le_mul_of_nonneg_right
                (mul_le_mul
                  (pairShape_abs_le_envelope a b z.1 ha hb)
                  (pairShape_abs_le_envelope c d z.2 hc hd)
                  (abs_nonneg _)
                  (by
                    obtain ⟨hs1, hs2⟩ := pairEnvelope_sPowers a b
                    rw [s_pair_shape _ _ z.1 hs1 hs2]
                    exact mul_nonneg
                      (sPairCoefficient_envelope_nonneg a b ha hb)
                      (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)))
                (hkernel_nn z))
      _ = GaussianPair.primitiveInteraction (pairEnvelope a b)
          (pairEnvelope c d) := rfl
  refine (habs.trans (envelope_primitive_bound a b c d ha hb hc hd)).trans ?_
  exact kappaPi_bound_le a b c d ha hb hc hd hrate1 hrate2

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
