import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceChartNineGram
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawGram

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceChartBudget
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates PreparationMeasure
open PreparationChartGuard PreparationPhaseScalar
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open scoped BigOperators Matrix RealInnerProductSpace

private theorem raw_norm_lower (a : NativeLie) :
    (∑ i : Fin 12,(rawCoordinates a i)^2) ≤ ‖a‖^2 := by
  have pair := original_raw_inner (rawCoordinates a) (rawCoordinates a)
  rw [rawCoordinates.symm_apply_apply,real_inner_self_eq_norm_sq] at pair
  norm_num [Fin.sum_univ_succ] at pair ⊢
  change (rawCoordinates a 0)^2+((rawCoordinates a 1)^2+((rawCoordinates a 2)^2+
    ((rawCoordinates a 3)^2+((rawCoordinates a 4)^2+((rawCoordinates a 5)^2+
    ((rawCoordinates a 6)^2+((rawCoordinates a 7)^2+((rawCoordinates a 8)^2+
    ((rawCoordinates a 9)^2+((rawCoordinates a 10)^2+(rawCoordinates a 11)^2)))))))))) ≤ ‖a‖^2
  nlinarith [sq_nonneg (rawCoordinates a 0),sq_nonneg (rawCoordinates a 1),
    sq_nonneg (rawCoordinates a 2),sq_nonneg (rawCoordinates a 3),sq_nonneg (rawCoordinates a 4),
    sq_nonneg (rawCoordinates a 5),sq_nonneg (rawCoordinates a 6+rawCoordinates a 7),
    sq_nonneg (rawCoordinates a 8),sq_nonneg (rawCoordinates a 9),sq_nonneg (rawCoordinates a 10)]

private theorem raw_coordinate_bound (a : NativeLie) (i : Fin 12) : |rawCoordinates a i| ≤ ‖a‖ := by
  have term := Finset.single_le_sum (s:=Finset.univ) (fun k _ => sq_nonneg (rawCoordinates a k))
    (Finset.mem_univ i)
  have source := raw_norm_lower a
  nlinarith [norm_nonneg a,abs_nonneg (rawCoordinates a i),sq_abs (rawCoordinates a i)]

private theorem normal_source_norm (i : Fin 9) : ‖normalBuild (sourceNormal i)‖ ≤ 2 := by
  have pair := original_raw_inner (rawCoordinates (normalBuild (sourceNormal i)))
    (rawCoordinates (normalBuild (sourceNormal i)))
  rw [rawCoordinates.symm_apply_apply,real_inner_self_eq_norm_sq] at pair
  change ‖normalBuild (sourceNormal i)‖^2=_ at pair
  have positive := norm_nonneg (normalBuild (sourceNormal i))
  let x := rawRead (normalBuild (sourceNormal i))
  change ‖normalBuild (sourceNormal i)‖^2=
    2*(x 0*x 0+x 1*x 1+x 2*x 2+x 3*x 3+x 4*x 4+x 5*x 5+
      x 6*x 6+x 7*x 7+x 8*x 8+x 9*x 9+x 10*x 10)+x 6*x 7+x 7*x 6+x 11*x 11 at pair
  simp only [x,rawRead,normalBuild,LinearEquiv.apply_symm_apply] at pair
  fin_cases i
  all_goals norm_num [sourceNormal,normalBuild,Pi.single_apply,PiLp.toLp_apply,Fin.ext_iff] at pair positive ⊢
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go] at pair
  all_goals norm_num at pair
  all_goals first | (rcases pair with pair | pair <;> nlinarith) | nlinarith

private theorem broken_source_norm (i : Fin 9) : ‖(sourceBroken i).val‖ ≤ 2 := by
  exact (broken.norm_orthogonalProjectionOnto_apply_le _).trans (normal_source_norm i)

private theorem sourceD9_entry_difference (z : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius) (i j : Fin 9) :
    |sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) i j-sourceD9 vacuum i j| ≤
      100000000*sourceRadius := by
  rw [sourceD9_add,Matrix.add_apply,add_sub_cancel_left]
  have orbitBound : ‖orbit (normalBuild (sourceNormal i))‖ ≤ 2 := by
    have original := normal_orbit_upper (sourceNormal i)
    have unit : ‖sourceNormal i‖=1 := by simp [sourceNormal,PiLp.norm_single]
    rw [unit] at original
    simpa only [mul_one] using original
  have rawTotal : (∑ k : Fin 12,|rawCoordinates (sourceBroken j).val k|) ≤ 24 := by
    have point (k : Fin 12) : |rawCoordinates (sourceBroken j).val k| ≤ 2 :=
      (raw_coordinate_bound _ k).trans (broken_source_norm j)
    have total := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => point k)
    norm_num at total
    exact total
  have actionBound := actual_full_scalar_action_bound (sourceBroken j).val
    ((fullCoordinates.symm z).2.1 : Scalar)
  have scalarBound := scalar_box_norm z (closed_box_outer z zbox)
  have actionSize : ‖action ((fullCoordinates.symm z).2.1 : Scalar) (sourceBroken j).val‖ ≤
      45158400*sourceRadius := by
    calc
      _ ≤ 117600*(∑ k : Fin 12,|rawCoordinates (sourceBroken j).val k|)*
          ‖((fullCoordinates.symm z).2.1 : Scalar)‖ := actionBound
      _ ≤ 117600*24*(16*sourceRadius) := by gcongr
      _ = 45158400*sourceRadius := by ring
  have pairing := norm_inner_le_norm (𝕜:=ℝ) (orbit (normalBuild (sourceNormal i)))
    (action ((fullCoordinates.symm z).2.1 : Scalar) (sourceBroken j).val)
  change |sourceD9 ((fullCoordinates.symm z).2.1 : Scalar) i j| ≤ _
  change |inner ℝ (orbit (normalBuild (sourceNormal i)))
    (action ((fullCoordinates.symm z).2.1 : Scalar) (sourceBroken j).val)| ≤ _ at pairing
  have product := mul_le_mul orbitBound actionSize
    (norm_nonneg (action ((fullCoordinates.symm z).2.1 : Scalar) (sourceBroken j).val))
    (by norm_num : (0 : ℝ) ≤ 2)
  exact pairing.trans (product.trans (by nlinarith [radius_small.1]))

private theorem product_difference_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (L epsilon : ℝ) (large : 1 ≤ L) (positive : 0 ≤ epsilon)
    (hf : ∀ i∈s,|f i| ≤ L) (hg : ∀ i∈s,|g i| ≤ L)
    (difference : ∀ i∈s,|f i-g i| ≤ epsilon) :
    |(∏ i∈s,f i)-(∏ i∈s,g i)| ≤ (s.card : ℝ)*epsilon*L^s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have left := hf i (Finset.mem_insert_self i s)
    have right := hg i (Finset.mem_insert_self i s)
    have diff := difference i (Finset.mem_insert_self i s)
    have tail := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => difference j (Finset.mem_insert_of_mem hj))
    have product : |∏ j∈s,f j| ≤ L^s.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _j∈s,L := Finset.prod_le_prod (fun j _ => abs_nonneg (f j))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ = L^s.card := by simp
    have equation : f i*(∏ j∈s,f j)-g i*(∏ j∈s,g j)=
        (f i-g i)*(∏ j∈s,f j)+g i*((∏ j∈s,f j)-(∏ j∈s,g j)) := by ring
    rw [Finset.prod_insert hi,Finset.prod_insert hi,equation,Finset.card_insert_of_notMem hi]
    have first := mul_le_mul diff product (abs_nonneg _) positive
    have second := mul_le_mul right tail (abs_nonneg _) (by linarith : 0 ≤ L)
    have extra : epsilon*L^s.card ≤ L*epsilon*L^s.card := by
      nlinarith [mul_nonneg positive (pow_nonneg (by linarith : 0 ≤ L) s.card)]
    calc
      _ ≤ |(f i-g i)*(∏ j∈s,f j)|+|g i*((∏ j∈s,f j)-(∏ j∈s,g j))| := abs_add_le _ _
      _ ≤ epsilon*L^s.card+L*((s.card : ℝ)*epsilon*L^s.card) := by
        rw [abs_mul,abs_mul]
        exact add_le_add first second
      _ ≤ L*epsilon*L^s.card+L*((s.card : ℝ)*epsilon*L^s.card) := add_le_add extra le_rfl
      _ = ((s.card+1 : ℕ) : ℝ)*epsilon*L^(s.card+1) := by push_cast; rw [pow_succ]; ring

private theorem determinant_difference_bound (A B : Matrix (Fin 9) (Fin 9) ℝ) (epsilon : ℝ)
    (positive : 0 ≤ epsilon) (ha : ∀ i j,|A i j| ≤ 5) (hb : ∀ i j,|B i j| ≤ 5)
    (difference : ∀ i j,|A i j-B i j| ≤ epsilon) :
    |A.det-B.det| ≤ (Nat.factorial 9 : ℝ)*9*epsilon*5^9 := by
  rw [Matrix.det_apply',Matrix.det_apply',←Finset.sum_sub_distrib]
  have terms (sigma : Equiv.Perm (Fin 9)) :
      |(Equiv.Perm.sign sigma : ℝ)*(∏ i : Fin 9,A (sigma i) i)-
        (Equiv.Perm.sign sigma : ℝ)*(∏ i : Fin 9,B (sigma i) i)| ≤ 9*epsilon*5^9 := by
    rw [←mul_sub,abs_mul,abs_unit_intCast,one_mul]
    have bound := product_difference_bound Finset.univ
      (fun i => A (sigma i) i) (fun i => B (sigma i) i) 5 epsilon (by norm_num) positive
      (fun i _ => ha (sigma i) i) (fun i _ => hb (sigma i) i) (fun i _ => difference (sigma i) i)
    simpa using bound
  calc
    _ ≤ ∑ sigma : Equiv.Perm (Fin 9),|(Equiv.Perm.sign sigma : ℝ)*(∏ i : Fin 9,A (sigma i) i)-
        (Equiv.Perm.sign sigma : ℝ)*(∏ i : Fin 9,B (sigma i) i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _sigma : Equiv.Perm (Fin 9),9*epsilon*5^9 := Finset.sum_le_sum (fun sigma _ => terms sigma)
    _ = (Nat.factorial 9 : ℝ)*9*epsilon*5^9 := by simp [Fintype.card_perm,mul_assoc]

theorem sourceD9_j15 (z : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius) :
    (1/15 : ℝ) ≤ (sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar))).det := by
  let A := sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar))
  have small : 100000000*sourceRadius ≤ 1 := by nlinarith [phase_radius]
  have ha (i j : Fin 9) : |A i j| ≤ 5 := by
    have difference := sourceD9_entry_difference z zbox i j
    rw [sourceGram_actual] at difference
    have triangle := real_abs_sub_le_sum (A i j-sourceGram i j) (-sourceGram i j)
    rw [abs_neg] at triangle
    have target : |A i j| ≤ |A i j-sourceGram i j|+|sourceGram i j| := by
      convert! triangle using 1
      congr 1
      ring
    exact target.trans (by linarith [sourceGram_entry_bound i j])
  have hb (i j : Fin 9) : |sourceGram i j| ≤ 5 := (sourceGram_entry_bound i j).trans (by norm_num)
  have difference := determinant_difference_bound A sourceGram (100000000*sourceRadius)
    (by nlinarith [radius_small.1]) ha hb (fun i j => by
      rw [←sourceGram_actual]
      exact sourceD9_entry_difference z zbox i j)
  rw [sourceGram_det] at difference
  have lower := (abs_le.mp difference).1
  change (1/15 : ℝ) ≤ A.det
  norm_num at lower
  nlinarith [phase_radius]

theorem sourceD9_inverse_zero (z : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius) :
    |((sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar))).det)⁻¹| ≤ 15 := by
  have guard := sourceD9_j15 z zbox
  have positive : 0 < (sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar))).det := by linarith
  rw [abs_of_pos (inv_pos.mpr positive)]
  have bound := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/15) guard
  norm_num [one_div] at bound
  exact bound

end LowEnergy.PreparationVacuumSourceChartBudget
