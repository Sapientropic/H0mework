import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraDualRead
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra
open scoped BigOperators Matrix

private theorem rigidstarEnd_nat (n : ℕ) : (starRingEnd ℂ) (n : ℂ) = n :=
  map_natCast (starRingEnd ℂ) n
private theorem rigidstarEnd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (starRingEnd ℂ) (ofNat(n) : ℂ) = ofNat(n) := map_ofNat (starRingEnd ℂ) n

private theorem source_form_star (t : Fin 4) (a : Fin 97) :
    star (dualSourceForm t a) = dualSourceForm t a := by
  unfold dualSourceForm
  split <;> norm_num [rigidstarEnd_nat,rigidstarEnd_ofNat]

private theorem pair_form_star (t u : Fin 4) : star (dualPairForm t u) = dualPairForm t u := by
  unfold dualPairForm
  split <;> norm_num [rigidstarEnd_nat,rigidstarEnd_ofNat]

private theorem sqrt2_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private theorem sqrt15_sq : (Real.sqrt 15 : ℂ)^2 = 15 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private theorem sqrt30_factor : (Real.sqrt 30 : ℂ) = (Real.sqrt 2 : ℂ)*(Real.sqrt 15 : ℂ) := by
  norm_cast
  rw [←Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem primal_dual_form_pair (t u : Fin 4) :
    (∑a : Fin 97,∑b : Fin 97,dualSourceForm t a*pairPoint false a b*dualSourceForm u b) =
      dualPairForm t u := by
  rw [actual_dual_form_pair_return]
  fin_cases t <;> fin_cases u <;>
    norm_num [dualSourceRead,dualPairForm,pairPoint,primalPairPoint,rigidstarEnd_nat,rigidstarEnd_ofNat,pairRow73,pairRow74,pairRow75,pairRow79,pairRow83,pairRow84,pairRow86,pairRow88,pairRow90,pairRow93,pairRow94,pairRow95,pairCoefficient1,pairCoefficient2,pairCoefficient5,pairCoefficient7,pairCoefficient8,pairCoefficient9,pairCoefficient10,pairCoefficient17,pairCoefficient18,pairCoefficient19,pairCoefficient20,pairCoefficient30,pairCoefficient37,pairCoefficient38,pairCoefficient39,pairCoefficient40,pairCoefficient41,pairCoefficient42,pairCoefficient46,pairCoefficient47,pairCoefficient48,pairCoefficient49,pairCoefficient50,pairCoefficient51,pairCoefficient52,pairCoefficient53,pairCoefficient54,pairCoefficient57,pairCoefficient62,pairCoefficient63,pairCoefficient64,pairCoefficient65,pairCoefficient66,pairCoefficient67,pairCoefficient68,pairCoefficient69,pairCoefficient71,pairCoefficient75,pairCoefficient76,pairCoefficient81,pairCoefficient82,pairCoefficient84,pairCoefficient86,pairCoefficient88,pairCoefficient89,pairCoefficient97,pairCoefficient111,pairCoefficient113,pairCoefficient115,pairCoefficient117,pairCoefficient124,pairCoefficient130,pairCoefficient131,pairCoefficient133,pairCoefficient134,pairCoefficient139,pairCoefficient142,pairCoefficient144,pairCoefficient149,pairCoefficient154,pairCoefficient155,pairCoefficient156,pairCoefficient162,pairCoefficient164,pairCoefficient165,pairCoefficient166,pairCoefficient167,pairCoefficient168,pairCoefficient169,pairCoefficient170,pairCoefficient171,pairCoefficient172,pairCoefficient173,pairCoefficient176,pairCoefficient177,pairCoefficient178,pairCoefficient179,pairCoefficient180]
  all_goals repeat rw [sqrt30_factor]
  all_goals try ring_nf
  all_goals norm_num [sqrt2_sq,sqrt15_sq,Complex.I_sq]

theorem actual_dual_form_pair (t u : Fin 4) (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,dualSourceForm t a*pairPoint dual a b*dualSourceForm u b) =
      dualPairForm t u := by
  cases dual
  · exact primal_dual_form_pair t u
  · calc
      _ = star (∑a : Fin 97,∑b : Fin 97,
          dualSourceForm t a*pairPoint false a b*dualSourceForm u b) := by
        simp only [star_sum,star_mul,source_form_star]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        change dualSourceForm t a * star (primalPairPoint a b) * dualSourceForm u b =
          dualSourceForm u b * (star (primalPairPoint a b) * dualSourceForm t a)
        ring
      _ = star (dualPairForm t u) := congrArg star (primal_dual_form_pair t u)
      _ = _ := pair_form_star t u

end LowEnergy.ActualBraContactDualContraction
