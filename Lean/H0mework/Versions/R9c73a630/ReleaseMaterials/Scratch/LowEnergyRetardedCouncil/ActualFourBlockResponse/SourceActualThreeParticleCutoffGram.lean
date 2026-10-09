import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleResponse
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCutoffDilationWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffGram
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussDiagonalHistory GaussYukawaGrade GaussYukawaInteraction GaussCoreLabel
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open FullYSourceCutoffVolterra SourceCutoffDilationWard NamedColorQtNext NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceResolventBandLimit
open scoped BigOperators InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] embed GaussCoreLabel.project NativeHistoryGrade.projection
  GaussGradedCompression.compression GaussYukawaGrade.grade

/-- The actual bounded cutoff, interleaved with the unchanged original compression inverse. -/
def step (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H := -(finiteResolvent F z * cutoff n)
def shift (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H :=
  GaussGradedCompression.compression F + cutoff n - z • 1
/-- All 57 terms precede the Number-three restriction. -/
def inverse (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H :=
  (∑j ∈ Finset.range 57,(step F n z)^j) * finiteResolvent F z

def coreStep (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) : End :=
  -(resolventCore F z hz * nativeCutoffAction n)
def leg (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) (j : ℕ) : QuantumTest :=
  ((coreStep F n z hz)^j) (resolventCore F z hz q)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) :
    embed (resolventCore F z hz q) = finiteResolvent F z (embed q) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolvent_grade (F : Index) (z : ℂ) (hz : z.im ≠ 0) :
    Commute GaussYukawaGrade.grade (finiteResolvent F z) := by
  have hc := (source_compression_grade F).sub_right
    ((Commute.one_right GaussYukawaGrade.grade).smul_right z)
  obtain ⟨u,hu⟩ := resolvent_isUnit (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←hu] at hc ⊢
  rw [Ring.inverse_unit]
  exact hc.units_inv_right

private theorem raises_product {R : Type*} [Ring R] (G U Y : R)
    (hU : G*U=U*G) (hY : G*Y=Y*G+Y) : G*(-(U*Y))=(-(U*Y))*G+(-(U*Y)) := by
  calc
    _ = -(U*(G*Y)) := by rw [_root_.mul_neg,←mul_assoc,hU,mul_assoc]
    _ = -(U*(Y*G+Y)) := by rw [hY]
    _ = _ := by simp only [_root_.mul_add,neg_add,_root_.neg_mul,mul_assoc]

private theorem raises_power {R : Type*} [Ring R] [Algebra ℂ R] (G T : R)
    (h : G*T=T*G+T) (j : ℕ) : G*T^j=T^j*G+(j : ℂ) • T^j := by
  induction j with
  | zero => simp only [pow_zero,mul_one,one_mul,Nat.cast_zero,zero_smul,add_zero]
  | succ j ih =>
    rw [pow_succ,←mul_assoc,ih,add_mul,mul_assoc _ G _,h]
    simp only [mul_add,smul_mul_assoc,Nat.cast_add,Nat.cast_one,add_smul,one_smul,←mul_assoc]
    abel

private theorem step_raises (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    GaussYukawaGrade.grade * step F n z =
      step F n z * GaussYukawaGrade.grade + step F n z :=
  raises_product _ _ _ (resolvent_grade F z hz).eq (cutoff_raises n)

private theorem power_raises (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (j : ℕ) :
    GaussYukawaGrade.grade * (step F n z)^j =
      (step F n z)^j * GaussYukawaGrade.grade + (j : ℂ) • (step F n z)^j :=
  raises_power _ _ (step_raises F n z hz) j

theorem actual_cutoff_step_nilpotent (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    (step F n z)^57 = 0 :=
  source_homogeneous_zero _ 57 (power_raises F n z hz 57) (by decide)

private theorem factor_inverse {R : Type*} [Ring R] (D U Y : R) (h : D*U=1) :
    D+Y=D*(1-(-(U*Y))) := by
  rw [sub_neg_eq_add,mul_add,mul_one,←mul_assoc,h,one_mul]

private theorem source_factor (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    shift F n z = (GaussGradedCompression.compression F-z • 1)*(1-step F n z) := by
  have he : shift F n z = (GaussGradedCompression.compression F-z • 1)+cutoff n := by
    unfold shift
    abel
  rw [he]
  exact factor_inverse _ _ _ (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)

/-- This is an inverse of the actual original C_F+Y_n-z, before restricting its input. -/
theorem actual_cutoff_left_inverse (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    inverse F n z * shift F n z = 1 := by
  rw [source_factor F n z hz,inverse]
  calc
    _ = (∑j ∈ Finset.range 57,(step F n z)^j) *
        (finiteResolvent F z*(GaussGradedCompression.compression F-z • 1))*(1-step F n z) := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [show finiteResolvent F z*(GaussGradedCompression.compression F-z • 1)=1 from
        resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz,
        mul_one,geom_sum_mul_neg,actual_cutoff_step_nilpotent F n z hz,sub_zero]

theorem actual_cutoff_right_inverse (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    shift F n z * inverse F n z = 1 := by
  rw [source_factor F n z hz,inverse]
  calc
    _ = (GaussGradedCompression.compression F-z • 1)*
        ((1-step F n z)*(∑j ∈ Finset.range 57,(step F n z)^j))*finiteResolvent F z := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [mul_neg_geom_sum,actual_cutoff_step_nilpotent F n z hz,sub_zero,mul_one]
      exact resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz

private theorem core_step_embed (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) :
    embed (coreStep F n z hz q) = step F n z (embed q) := by
  simp only [coreStep,LinearMap.neg_apply,Module.End.mul_apply,map_neg,resolvent_embed]
  rw [←native_cutoff_core]
  rfl

theorem actual_leg_embed (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) (j : ℕ) :
    embed (leg F n z hz q j) = ((step F n z)^j) (finiteResolvent F z (embed q)) := by
  induction j with
  | zero => simpa only [leg,pow_zero,Module.End.one_apply,one_apply_eq_self] using resolvent_embed F z hz q
  | succ j ih =>
    change embed (((coreStep F n z hz)^(j+1)) (resolventCore F z hz q)) = _
    rw [pow_succ',Module.End.mul_apply,core_step_embed]
    change step F n z (embed (leg F n z hz q j)) = _
    rw [ih,pow_succ',mul_apply_eq_comp]

private theorem inverse_sector (l : Label) (q : QuantumTest) (hq : project l q=q) :
    project l (GaussRadialDomain.inverseAction q) = GaussRadialDomain.inverseAction q := by
  apply DFunLike.ext
  intro x
  have h := congrArg (fun f : QuantumTest => f x) hq
  simp only [project_apply] at h
  rw [project_apply]
  change fiberPiece l ((GaussRadialDomain.reciprocal x : ℂ) • q x) =
    (GaussRadialDomain.reciprocal x : ℂ) • q x
  rw [map_smul,h]

private theorem normalized_action (q : QuantumTest) :
    GaussYukawaCoefficient.action q = GaussRadialDomain.inverseAction (GaussYukawaOperator.originalAction q) := by
  apply DFunLike.ext
  intro x
  change GaussYukawaCoefficient.normalized x (q x) =
    GaussRadialDomain.inverseFiber x (GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField x) (q x))
  simp only [GaussYukawaCoefficient.normalized,GaussYukawaCoefficient.normalizedScalar,map_smul,
    smul_apply,GaussRadialDomain.inverseFiber]
  rfl

private theorem cutoff_sector (n : ℕ) (a : Fin 505) (k : Fin 57) (hk : k.val+1<57)
    (q : QuantumTest) (hq : project (a,k) q=q) :
    project (a,⟨k.val+1,hk⟩) (nativeCutoffAction n q)=nativeCutoffAction n q := by
  have hy : project (a,⟨k.val+1,hk⟩) (GaussYukawaCoefficient.action q)=GaussYukawaCoefficient.action q := by
    rw [normalized_action]
    exact inverse_sector _ _ (actual_Y_sector_successor a k hk q hq)
  induction n with
  | zero => exact hy
  | succ n ih =>
    change project _ (GaussYukawaCoefficient.action q+(nativeCutoffAction n q-
      GaussRadialDomain.inverseAction (nativeCutoffAction n q))) = _
    simp only [map_add,map_sub,hy,ih,inverse_sector _ _ ih]
    rfl

private theorem step_sector (F : Index) (n : ℕ) (a : Fin 505) (k : Fin 57) (hk : k.val+1<57)
    (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) (hq : project (a,k) q=q) :
    project (a,⟨k.val+1,hk⟩) (coreStep F n z hz q)=coreStep F n z hz q := by
  have h := actual_resolvent_sector F (a,⟨k.val+1,hk⟩) z hz _ (cutoff_sector n a k hk q hq)
  simpa only [coreStep,LinearMap.neg_apply,Module.End.mul_apply,map_neg] using congrArg Neg.neg h

theorem actual_leg_sector (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    ∀j : ℕ,∀hj : j<57,project (3,⟨j,hj⟩) (leg F n z hz q j)=leg F n z hz q j := by
  intro j
  induction j with
  | zero => intro hj; exact actual_resolvent_sector F (3,0) z hz q hq
  | succ j ih =>
    intro hj
    have h := step_sector F n 3 ⟨j,by omega⟩ hj z hz (leg F n z hz q j) (ih (by omega))
    simpa only [leg,pow_succ',Module.End.mul_apply] using h

theorem actual_fourth_leg_zero (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) : leg F n z hz q 4=0 :=
  (actual_leg_sector F n z hz q hq 4 (by decide)).symm.trans (actual_empty_sector 3 4 (by decide) _)

private theorem long_leg_zero (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) (j : ℕ) (hj : 4≤j) : leg F n z hz q j=0 := by
  change ((coreStep F n z hz)^j) (resolventCore F z hz q)=0
  calc
    _ = ((coreStep F n z hz)^(j-4)*(coreStep F n z hz)^4) (resolventCore F z hz q) := by
      rw [←pow_add,Nat.sub_add_cancel hj]
    _ = ((coreStep F n z hz)^(j-4)) (leg F n z hz q 4) := rfl
    _ = 0 := by rw [actual_fourth_leg_zero F n z hz q hq,map_zero]

/-- The genuine 57-term inverse has four and exactly four possible Number-three grades. -/
theorem actual_full_response (F : Index) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    inverse F n z (embed q)=∑j : Fin 4,embed (leg F n z hz q j.val) := by
  simp only [inverse,mul_apply_eq_comp,sum_apply]
  simp_rw [←actual_leg_embed F n z hz q]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => embed (leg F n z hz q j)) 4]
  symm
  apply Finset.sum_subset (Finset.range_mono (by decide : 4≤57))
  intro j _ hj
  rw [long_leg_zero F n z hz q hq j (by simpa only [Finset.mem_range,not_lt] using hj),map_zero]

/-- Both cutoffs use the same C_F and source; only the three positive Y grades remain. -/
def differenceLeg (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (j : ℕ) : QuantumTest := leg F ell z hz q j-leg F m z hz q j

private theorem difference_sector (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) (j : Fin 3) :
    project (3,⟨j.val+1,by omega⟩) (differenceLeg F m ell z hz q (j.val+1))=
      differenceLeg F m ell z hz q (j.val+1) := by
  simp only [differenceLeg,map_sub,actual_leg_sector F ell z hz q hq (j.val+1) (by omega),
    actual_leg_sector F m z hz q hq (j.val+1) (by omega)]

theorem actual_response_difference (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    inverse F ell z (embed q)-inverse F m z (embed q)=
      ∑j : Fin 3,embed (differenceLeg F m ell z hz q (j.val+1)) := by
  rw [actual_full_response F ell z hz q hq,actual_full_response F m z hz q hq,
    ←Finset.sum_sub_distrib,Fin.sum_univ_succ]
  simp only [leg,Fin.val_zero,pow_zero,Module.End.one_apply,sub_self,zero_add,
    differenceLeg,Fin.val_succ,map_sub]

private theorem cross_difference_zero (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q r : QuantumTest) (hq : project (3,0) q=q) (hr : project (3,0) r=r)
    (i j : Fin 3) (hij : i≠j) :
    inner ℂ (embed (differenceLeg F m ell z hz q (i.val+1)))
      (embed (differenceLeg F m ell z hz r (j.val+1)))=0 := by
  let li : Label := (3,⟨i.val+1,by omega⟩)
  let lj : Label := (3,⟨j.val+1,by omega⟩)
  have hi : projection li (embed (differenceLeg F m ell z hz q (i.val+1)))=
      embed (differenceLeg F m ell z hz q (i.val+1)) :=
    (embed_project li _).symm.trans (congrArg embed (difference_sector F m ell z hz q hq i))
  have hj : projection lj (embed (differenceLeg F m ell z hz r (j.val+1)))=
      embed (differenceLeg F m ell z hz r (j.val+1)) :=
    (embed_project lj _).symm.trans (congrArg embed (difference_sector F m ell z hz r hr j))
  have hneq : li≠lj := by
    intro h
    apply hij
    apply Fin.ext
    have he := congrArg (fun l : Label => l.2.val) h
    dsimp only [li,lj] at he
    omega
  have hp := congrArg (fun T : H →L[ℂ] H => T (embed (differenceLeg F m ell z hz r (j.val+1))))
    (projection_product li lj)
  simp only [if_neg hneq,mul_apply_eq_comp,zero_apply,hj] at hp
  calc
    _ = inner ℂ (projection li (embed (differenceLeg F m ell z hz q (i.val+1))))
        (embed (differenceLeg F m ell z hz r (j.val+1))) := by rw [hi]
    _ = inner ℂ (embed (differenceLeg F m ell z hz q (i.val+1)))
        (projection li (embed (differenceLeg F m ell z hz r (j.val+1)))) := projection_symmetric li _ _
    _ = 0 := by rw [hp,inner_zero_right]

/-- Same-grade complex interference is retained; orthogonality removes only different actual grades. -/
theorem actual_response_difference_gram (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q r : QuantumTest) (hq : project (3,0) q=q) (hr : project (3,0) r=r) :
    inner ℂ (inverse F ell z (embed q)-inverse F m z (embed q))
      (inverse F ell z (embed r)-inverse F m z (embed r))=
      ∑j : Fin 3,inner ℂ (embed (differenceLeg F m ell z hz q (j.val+1)))
        (embed (differenceLeg F m ell z hz r (j.val+1))) := by
  rw [actual_response_difference F m ell z hz q hq,actual_response_difference F m ell z hz r hr,sum_inner]
  simp only [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact cross_difference_zero F m ell z hz q r hq hr i j (Ne.symm hji)
  · simp

theorem actual_response_difference_norm (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖inverse F ell z (embed q)-inverse F m z (embed q)‖^2=
      ∑j : Fin 3,‖embed (differenceLeg F m ell z hz q (j.val+1))‖^2 := by
  have h := actual_response_difference_gram F m ell z hz q q hq hq
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The cutoff core legs are the representatives of the paid wholeWord families. -/
theorem actual_mixed_word_leg (F : Index) (n j : ℕ) (μ w : ℝ) (hμ : 0<μ) (q : QuantumTest) :
    embed (leg F n (line μ w) (by simpa only [line_im] using ne_of_gt hμ) q j)=
      (-1 : ℂ)^j • (mixedWord F μ w (List.replicate j (false,n)) (embed q)) := by
  induction j with
  | zero =>
    simpa only [leg,pow_zero,Module.End.one_apply,one_smul,mixedWord,
      List.replicate_zero,List.map_nil,word,finiteResolvent] using resolvent_embed F (line μ w) _ q
  | succ j ih =>
    change embed (((coreStep F n (line μ w) _)^(j+1)) (resolventCore F (line μ w) _ q)) = _
    rw [pow_succ',Module.End.mul_apply,core_step_embed]
    change -(finiteResolvent F (line μ w) (cutoff n (embed (leg F n (line μ w) _ q j)))) = _
    rw [ih]
    simp only [mixedWord,List.replicate_succ,List.map_cons,mixedLetter,Bool.false_eq_true,ite_false,
      word,mul_apply_eq_comp,map_smul,pow_succ,mul_neg_one,neg_smul,finiteResolvent]

end LowEnergy.ActualThreeParticleCutoffGram
