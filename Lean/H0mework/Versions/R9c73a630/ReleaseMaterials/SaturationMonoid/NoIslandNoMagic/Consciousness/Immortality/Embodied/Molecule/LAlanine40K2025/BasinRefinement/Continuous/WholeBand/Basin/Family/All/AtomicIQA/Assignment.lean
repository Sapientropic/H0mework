import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open SourceGaussianModel SourceExponential WholeBandAttractor Set Metric Function MeasureTheory
noncomputable section

/-- Integer basin-centre table read off the thirteen reifier-declared `rawCenter`
    arrays on the `2^160` grid: `centreInt i k = centre(i)_k * 2^160`. -/
def centreInt (i : Fin 13) (k : Fin 3) : ℤ :=
  if i=0 then Atom000.Point.rawCenter[k.val]! else
  if i=1 then Atom001.Point.rawCenter[k.val]! else
  if i=2 then Atom002.Point.rawCenter[k.val]! else
  if i=3 then Atom003.Point.rawCenter[k.val]! else
  if i=4 then Atom004.Point.rawCenter[k.val]! else
  if i=5 then Atom005.Point.rawCenter[k.val]! else
  if i=6 then Atom006.Point.rawCenter[k.val]! else
  if i=7 then Atom007.Point.rawCenter[k.val]! else
  if i=8 then Atom008.Point.rawCenter[k.val]! else
  if i=9 then Atom009.Point.rawCenter[k.val]! else
  if i=10 then Atom010.Point.rawCenter[k.val]! else
  if i=11 then Atom011.Point.rawCenter[k.val]! else
  Atom012.Point.rawCenter[k.val]!

/-- The basin centre is the reifier integer centre divided by the `2^160` grid
    scale, coordinate by coordinate. -/
theorem source_centre_coord (i : Fin 13) (k : Fin 3) :
    sourceCentre i k = ((centreInt i k : ℚ)/(2^160 : ℚ) : ℝ) := by
  fin_cases i <;> fin_cases k <;>
    simp [sourceCentre,centreInt,SourceExponential.scale,
      Atom000.centre,Atom000.centreRat,Atom001.centre,Atom001.centreRat,
      Atom002.centre,Atom002.centreRat,Atom003.centre,Atom003.centreRat,
      Atom004.centre,Atom004.centreRat,Atom005.centre,Atom005.centreRat,
      Atom006.centre,Atom006.centreRat,Atom007.centre,Atom007.centreRat,
      Atom008.centre,Atom008.centreRat,Atom009.centre,Atom009.centreRat,
      Atom010.centre,Atom010.centreRat,Atom011.centre,Atom011.centreRat,
      Atom012.centre,Atom012.centreRat]

/-- Kernel-checked integer certificate: every basin centre coordinate sits within
    `699/10000` bohr of its own nucleus (`centre*10^12 - position*2^160` bounded by
    `699 * 2^160 * 10^8`). -/
theorem centre_own_gap_certified :
    ∀ i : Fin 13, ∀ k : Fin 3,
      |centreInt i k * (10^12 : ℤ) - Nuclear.positionTable i k * (2^160 : ℤ)| ≤
        699 * (2^160 : ℤ) * 10^8 := by
  decide +kernel

/-- Kernel-checked integer certificate: heavy nuclei (charge > 1, indices
    0,1,2,6,7,9) have their basin centre within `9/10^6` bohr of the nucleus. -/
theorem centre_own_gap_heavy :
    ∀ i : Fin 13, ∀ k : Fin 3, 1 < Nuclear.nuclearChargeNat i →
      |centreInt i k * (10^12 : ℤ) - Nuclear.positionTable i k * (2^160 : ℤ)| ≤
        9 * (2^160 : ℤ) * 10^6 := by
  decide +kernel

/-- Kernel-checked integer certificate: for every distinct pair `(i,j)` some
    coordinate has `|centre_i,k - position_j,k| ≥ 5/4` bohr
    (`125 * 2^160 * 10^10` on the integer grid). -/
theorem centre_other_gap_certified :
    ∀ i : Fin 13, ∀ j : Fin 13, i ≠ j →
      (125 * (2^160 : ℤ) * 10^10) ≤
        |centreInt i 0 * (10^12 : ℤ) - Nuclear.positionTable j 0 * (2^160 : ℤ)| ∨
      (125 * (2^160 : ℤ) * 10^10) ≤
        |centreInt i 1 * (10^12 : ℤ) - Nuclear.positionTable j 1 * (2^160 : ℤ)| ∨
      (125 * (2^160 : ℤ) * 10^10) ≤
        |centreInt i 2 * (10^12 : ℤ) - Nuclear.positionTable j 2 * (2^160 : ℤ)| := by
  decide +kernel

/-- Integer grid bound lifts to a rational coordinate bound. -/
private theorem grid_gap_bound {n p N : ℤ} {B : ℚ}
    (hN : (N : ℚ) = B * (2^160 : ℚ) * 10^12)
    (h : |n * (10^12 : ℤ) - p * (2^160 : ℤ)| ≤ N) :
    |(n : ℚ)/2^160 - (p : ℚ)/10^12| ≤ B := by
  have key : (n : ℚ)/2^160 - (p : ℚ)/10^12 =
      ((n * 10^12 - p * 2^160 : ℤ) : ℚ) / ((2^160 : ℚ) * 10^12) := by
    field_simp
    push_cast
    ring
  have hnum : |((n * 10^12 - p * 2^160 : ℤ) : ℚ)| ≤ (N : ℚ) := by exact_mod_cast h
  rw [key,abs_div]
  rw [show |(2^160 : ℚ) * 10^12| = (2^160 : ℚ) * 10^12 from abs_of_pos (by norm_num)]
  rw [div_le_iff₀ (by norm_num : (0:ℚ) < 2^160 * 10^12)]
  rw [show B * ((2^160 : ℚ) * 10^12) = (N : ℚ) from by rw [hN]; ring]
  exact hnum

/-- Integer grid lower bound lifts to a rational coordinate lower bound. -/
private theorem grid_gap_lower {n p N : ℤ} {B : ℚ}
    (hN : (N : ℚ) = B * (2^160 : ℚ) * 10^12)
    (h : N ≤ |n * (10^12 : ℤ) - p * (2^160 : ℤ)|) :
    B ≤ |(n : ℚ)/2^160 - (p : ℚ)/10^12| := by
  have key : (n : ℚ)/2^160 - (p : ℚ)/10^12 =
      ((n * 10^12 - p * 2^160 : ℤ) : ℚ) / ((2^160 : ℚ) * 10^12) := by
    field_simp
    push_cast
    ring
  have hnum : (N : ℚ) ≤ |((n * 10^12 - p * 2^160 : ℤ) : ℚ)| := by exact_mod_cast h
  rw [key,abs_div]
  rw [show |(2^160 : ℚ) * 10^12| = (2^160 : ℚ) * 10^12 from abs_of_pos (by norm_num)]
  rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2^160 * 10^12)]
  rw [show B * ((2^160 : ℚ) * 10^12) = (N : ℚ) from by rw [hN]; ring]
  exact hnum

/-- The ledger picobohr table gives the physical nucleus coordinate. -/
private theorem position_coord (a : Fin 13) (k : Fin 3) :
    Nuclear.nuclearPosition a k =
      (((Nuclear.positionTable a k : ℤ) : ℚ)/10^12 : ℝ) := by
  change ((Nuclear.nuclearPositionQ a k : ℚ) : ℝ) = _
  rw [Nuclear.nuclearPositionQ_eq_table]
  push_cast
  ring

/-- Centre–nucleus coordinate gap, cast from the integer certificate. -/
private theorem coord_gap_le {i : Fin 13} {k : Fin 3} {j : Fin 13} {N : ℤ} {B : ℚ}
    (hN : (N : ℚ) = B * (2^160 : ℚ) * 10^12)
    (h : |centreInt i k * (10^12 : ℤ) - Nuclear.positionTable j k * (2^160 : ℤ)| ≤ N) :
    |sourceCentre i k - Nuclear.nuclearPosition j k| ≤ (B : ℝ) := by
  have hq : |(centreInt i k : ℚ)/2^160 - (Nuclear.positionTable j k : ℚ)/10^12| ≤ B :=
    grid_gap_bound hN h
  rw [source_centre_coord,position_coord]
  rw [show ((centreInt i k : ℚ)/(2^160:ℚ) : ℝ) -
      ((Nuclear.positionTable j k : ℚ)/10^12 : ℝ) =
      (((centreInt i k : ℚ)/2^160 - (Nuclear.positionTable j k : ℚ)/10^12 : ℚ) : ℝ) from
        by push_cast; ring]
  exact_mod_cast hq

/-- Centre–other-nucleus coordinate gap from below. -/
private theorem coord_gap_ge {i : Fin 13} {k : Fin 3} {j : Fin 13} {N : ℤ} {B : ℚ}
    (hN : (N : ℚ) = B * (2^160 : ℚ) * 10^12)
    (h : N ≤ |centreInt i k * (10^12 : ℤ) - Nuclear.positionTable j k * (2^160 : ℤ)|) :
    (B : ℝ) ≤ |sourceCentre i k - Nuclear.nuclearPosition j k| := by
  have hq : B ≤ |(centreInt i k : ℚ)/2^160 - (Nuclear.positionTable j k : ℚ)/10^12| :=
    grid_gap_lower hN h
  rw [source_centre_coord,position_coord]
  rw [show ((centreInt i k : ℚ)/(2^160:ℚ) : ℝ) -
      ((Nuclear.positionTable j k : ℚ)/10^12 : ℝ) =
      (((centreInt i k : ℚ)/2^160 - (Nuclear.positionTable j k : ℚ)/10^12 : ℚ) : ℝ) from
        by push_cast; ring]
  exact_mod_cast hq

private theorem rat_cast_699 : ((699/10000 : ℚ) : ℝ) = 699/10000 := by norm_num
private theorem rat_cast_9 : ((9/1000000 : ℚ) : ℝ) = 9/1000000 := by norm_num
private theorem rat_cast_54 : ((5/4 : ℚ) : ℝ) = 5/4 := by norm_num

theorem centre_own_nucleus_close (i : Fin 13) (k : Fin 3) :
    |sourceCentre i k - Nuclear.nuclearPosition i k| ≤ (699/10000 : ℝ) := by
  rw [← rat_cast_699]
  exact coord_gap_le (B := (699/10000 : ℚ)) (by norm_num)
    (centre_own_gap_certified i k)

theorem centre_own_nucleus_close_heavy (i : Fin 13) (k : Fin 3)
    (heavy : 1 < Nuclear.nuclearChargeNat i) :
    |sourceCentre i k - Nuclear.nuclearPosition i k| ≤ (9/1000000 : ℝ) := by
  rw [← rat_cast_9]
  exact coord_gap_le (B := (9/1000000 : ℚ)) (by norm_num)
    (centre_own_gap_heavy i k heavy)

theorem centre_far_from_other_nucleus (i j : Fin 13) (different : i ≠ j) :
    ∃ k : Fin 3, (5/4 : ℝ) ≤ |sourceCentre i k - Nuclear.nuclearPosition j k| := by
  rcases centre_other_gap_certified i j different with h | h | h
  · exact ⟨0,by rw [← rat_cast_54]; exact coord_gap_ge (B := (5/4 : ℚ)) (by norm_num) h⟩
  · exact ⟨1,by rw [← rat_cast_54]; exact coord_gap_ge (B := (5/4 : ℚ)) (by norm_num) h⟩
  · exact ⟨2,by rw [← rat_cast_54]; exact coord_gap_ge (B := (5/4 : ℚ)) (by norm_num) h⟩

private theorem attractor_coordinate_close (i : Fin 13) (k : Fin 3) :
    |(sourceSeed i).criticalPoint k - sourceCentre i k| ≤ sourceRadius := by
  have hinside := source_zero_inside i
  rw [mem_closedBall] at hinside
  have h := dist_le_pi_dist (sourceSeed i).criticalPoint (sourceCentre i) k
  rw [Real.dist_eq] at h
  exact h.trans hinside

/-- The source attractor of basin `i` lies within `7/100` bohr of nucleus `i`. -/
theorem attractor_near_own_nucleus (i : Fin 13) :
    dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition i) ≤ (7/100 : ℝ) := by
  rw [dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 7/100)]
  intro k
  have hstep := attractor_coordinate_close i k
  have hgap := centre_own_nucleus_close i k
  rw [Real.norm_eq_abs]
  rw [show |((sourceSeed i).criticalPoint - Nuclear.nuclearPosition i) k| =
      |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition i k| from rfl]
  calc |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition i k|
      ≤ |(sourceSeed i).criticalPoint k - sourceCentre i k| +
        |sourceCentre i k - Nuclear.nuclearPosition i k| := abs_sub_le _ _ _
    _ ≤ sourceRadius + 699/10000 := add_le_add hstep hgap
    _ ≤ 7/100 := by norm_num [sourceRadius]

/-- Heavy-atom attractors sit essentially on their nucleus. -/
theorem heavy_attractor_on_nucleus (i : Fin 13)
    (heavy : 1 < Nuclear.nuclearChargeNat i) :
    dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition i) ≤ (1/100000 : ℝ) := by
  rw [dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/100000)]
  intro k
  have hstep := attractor_coordinate_close i k
  have hgap := centre_own_nucleus_close_heavy i k heavy
  rw [Real.norm_eq_abs]
  rw [show |((sourceSeed i).criticalPoint - Nuclear.nuclearPosition i) k| =
      |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition i k| from rfl]
  calc |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition i k|
      ≤ |(sourceSeed i).criticalPoint k - sourceCentre i k| +
        |sourceCentre i k - Nuclear.nuclearPosition i k| := abs_sub_le _ _ _
    _ ≤ sourceRadius + 9/1000000 := add_le_add hstep hgap
    _ ≤ 1/100000 := by norm_num [sourceRadius]

/-- The source attractor of basin `i` is at least `6/5` bohr from every other
    nucleus — in sup norm, even after the basin-radius correction. -/
theorem attractor_far_from_other_nuclei (i j : Fin 13) (different : i ≠ j) :
    (6/5 : ℝ) ≤ dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition j) := by
  rcases centre_far_from_other_nucleus i j different with ⟨k,hk⟩
  have hstep := attractor_coordinate_close i k
  have hcoord : |sourceCentre i k - Nuclear.nuclearPosition j k| -
      |(sourceSeed i).criticalPoint k - sourceCentre i k| ≤
      |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition j k| := by
    have h := abs_sub_le (sourceCentre i k) ((sourceSeed i).criticalPoint k)
      (Nuclear.nuclearPosition j k)
    rw [abs_sub_comm (sourceCentre i k) ((sourceSeed i).criticalPoint k)] at h
    linarith [abs_nonneg ((sourceSeed i).criticalPoint k - Nuclear.nuclearPosition j k)]
  have hpi : |(sourceSeed i).criticalPoint k - Nuclear.nuclearPosition j k| ≤
      dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition j) := by
    have h := dist_le_pi_dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition j) k
    rwa [Real.dist_eq] at h
  have hradius : sourceRadius = (1/1048576 : ℝ) := rfl
  linarith

/-- Every source attractor is strictly nearest to its own nucleus: the basin↔atom
    assignment is unambiguous. -/
theorem attractor_nearest_nucleus (i j : Fin 13) (different : i ≠ j) :
    dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition i) <
      dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition j) :=
  lt_of_lt_of_le
    (lt_of_le_of_lt (attractor_near_own_nucleus i) (by norm_num : (7/100:ℝ) < 6/5))
    (attractor_far_from_other_nuclei i j different)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
