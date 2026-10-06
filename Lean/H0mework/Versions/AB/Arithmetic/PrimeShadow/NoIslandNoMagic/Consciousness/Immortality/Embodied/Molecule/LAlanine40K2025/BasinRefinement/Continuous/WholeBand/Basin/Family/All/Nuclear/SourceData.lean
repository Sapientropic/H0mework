import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceSourceBoundReentry
import H0mework.Versions.AB.Chemistry.LAlanineRefinementSource.FiniteData

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open SourceGaussianModel SourceFiniteData
open scoped BigOperators
noncomputable section

/-- Nuclear charge read from the same reentry occurrence's inertial step. -/
def nuclearChargeNat (a : Fin 13) : ℕ :=
  (Reentry.Source.nuclearReadout.targetNuclei[a.val]!).2

def nuclearCharge (a : Fin 13) : ℝ := nuclearChargeNat a

/-- The target ledger positions as a literal integer picobohr table. -/
def positionTable : Fin 13 → Fin 3 → ℤ :=
  ![![2617959752356, 6274094655365, 15876675783856],
    ![4115672357163, 3063830604983, 13549125743864],
    ![8949564327999, 3961626314993, 14797159576324],
    ![8773220412490, 3442875471193, 13200059869960],
    ![8693730872788, 2658248503458, 15839045216382],
    ![10511808404289, 4559429537581, 15021936548873],
    ![4382615129546, 5004516430417, 14873199081614],
    ![7074704103059, 5987723033555, 15340469085465],
    ![7227439806032, 6469784748961, 17127463707021],
    ![7632993489745, 8301635689536, 13711419203839],
    ![9295486538751, 8931844192723, 14094882100895],
    ![6402936681539, 9597797973590, 14052467948700],
    ![7552483388227, 7841611592145, 11953395125565]]

/-- The literal table is exactly the inertial step's target positions. -/
theorem position_table_same_source :
    ∀ a : Fin 13, ∀ k : Fin 3,
      Reentry.Source.nuclearReadout.targetPositionPicobohr a k =
        positionTable a k := by
  decide +kernel

/-- Ledger positions are integer picobohr; the physical position is in bohr. -/
def nuclearPositionQ (a : Fin 13) (k : Fin 3) : ℚ :=
  ((Reentry.Source.nuclearReadout.targetPositionPicobohr a k : ℤ) : ℚ) / 10 ^ 12

def nuclearPosition (a : Fin 13) : Point := fun k => nuclearPositionQ a k

theorem nuclearPositionQ_eq_table (a : Fin 13) (k : Fin 3) :
    nuclearPositionQ a k = ((positionTable a k : ℤ) : ℚ) / 10 ^ 12 := by
  simp only [nuclearPositionQ]
  rw [position_table_same_source]

theorem charge_census : (fun a : Fin 13 => nuclearChargeNat a) =
    ![8,8,7,1,1,1,6,6,1,6,1,1,1] := by
  funext a
  fin_cases a <;> decide

theorem total_nuclear_charge : ∑ a : Fin 13, nuclearCharge a = 48 := by
  have nat : ∑ a : Fin 13, nuclearChargeNat a = 48 := by
    rw [charge_census]
    decide
  simp only [nuclearCharge]
  exact_mod_cast nat

private theorem position_int_injective {x y : ℤ}
    (h : ((x : ℚ) / 10^12) = ((y : ℚ) / 10^12)) : x = y := by
  have hP : (10^12 : ℚ) ≠ 0 := by norm_num
  have casted : (x : ℚ) = (y : ℚ) := by
    have := congrArg (· * (10^12 : ℚ)) h
    rwa [div_mul_cancel₀ _ hP,div_mul_cancel₀ _ hP] at this
  exact_mod_cast casted

/-- Two recorded nuclei never occupy the same point: some coordinate differs
    already at integer picobohr precision. -/
theorem nuclear_positions_distinct (a b : Fin 13) (ne : a ≠ b) :
    nuclearPosition a ≠ nuclearPosition b := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl ne
    | (intro heq
       exact absurd (fun k : Fin 3 =>
         position_int_injective
           (Rat.cast_injective (congrFun heq k))) (by decide))

/-- Rational closeness certificate: `|n/d - p/10^12| ≤ 1/10^12` is exactly the
    integer check `|n·10^12 - p·d| ≤ d`, so kernel evaluation stays on `ℤ`. -/
private theorem centre_close_iff {n : ℤ} {d : ℕ} {p : ℤ} (hd : d ≠ 0) :
    (|n * (10^12 : ℤ) - p * (d : ℤ)| ≤ (d : ℤ)) ↔
      |((n : ℚ) / d - (p : ℚ) / 10^12)| ≤ (1 : ℚ) / 10^12 := by
  have hd0 : (0 : ℚ) < (d : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hP : (0 : ℚ) < (10^12 : ℚ) := by norm_num
  have key : (n : ℚ) / d - (p : ℚ) / 10^12 =
      ((n * (10^12 : ℤ) - p * (d : ℤ) : ℤ) : ℚ) / ((d : ℚ) * 10^12) := by
    field_simp
    push_cast
    ring
  rw [key,abs_div]
  rw [show |((d : ℚ) * 10^12)| = (d : ℚ) * 10^12 from abs_of_pos (mul_pos hd0 hP)]
  rw [div_le_iff₀ (mul_pos hd0 hP)]
  rw [show (1 / 10^12 : ℚ) * ((d : ℚ) * 10^12) = (d : ℚ) by field_simp]
  constructor <;> intro h <;> exact_mod_cast h

/-- Boolean certificate: every coordinate of `t.centre` sits within one
    picobohr of nucleus `a`, checked at integer level through num/den. -/
private def termOn (t : SourceGaussianModel.Term) (a : Fin 13) : Bool :=
  (List.finRange 3).all fun k =>
    decide (|(t.centre k).num * (10^12 : ℤ) -
        positionTable a k * ((t.centre k).den : ℤ)| ≤ ((t.centre k).den : ℤ))

private theorem termOn_iff (t : SourceGaussianModel.Term) (a : Fin 13) :
    termOn t a = true ↔
      ∀ k : Fin 3,
        |t.centre k - ((positionTable a k : ℤ) : ℚ) / 10^12| ≤ (1 : ℚ) / 10^12 := by
  simp only [termOn,List.all_eq_true,List.mem_finRange,true_implies,
    decide_eq_true_eq]
  constructor
  · intro h k
    have hq := (centre_close_iff (Rat.den_ne_zero (t.centre k))).mp (h k)
    rwa [Rat.num_div_den] at hq
  · intro h k
    have h' := h k
    rw [← Rat.num_div_den (t.centre k)] at h'
    exact (centre_close_iff (Rat.den_ne_zero (t.centre k))).mpr h'

/-- One kernel pass over all 208 source primitives: each is centred on some
    recorded nucleus within picobohr rounding. -/
private def allOn : Bool :=
  (List.finRange 98).all fun b =>
    (sourceTerms b).all fun t => (List.finRange 13).any (termOn t)

private theorem allOn_true : allOn = true := by
  decide +kernel

/-- Every original Gaussian primitive sits on one of the thirteen recorded
    nuclei, inside picobohr rounding. -/
theorem basis_centres_on_nuclei :
    ∀ b : Basis, ∀ t ∈ sourceTerms b,
      ∃ a : Fin 13, ∀ k : Fin 3,
        |t.centre k - nuclearPositionQ a k| ≤ (1 : ℚ) / 10^12 := by
  intro b t ht
  have hrow := (List.all_eq_true.mp allOn_true) b (List.mem_finRange b)
  have hterm := (List.all_eq_true.mp hrow) t ht
  obtain ⟨a,_,hon⟩ := List.any_eq_true.mp hterm
  refine ⟨a,fun k => ?_⟩
  rw [nuclearPositionQ_eq_table]
  exact (termOn_iff t a).mp hon k

/-- Countercontrol positions: every nucleus translated by `10⁻⁹` bohr along the
    first axis. -/
def shiftedNuclearPositionQ (a : Fin 13) (k : Fin 3) : ℚ :=
  nuclearPositionQ a k + (if k = 0 then (1 : ℚ) / 10^9 else 0)

private theorem shifted_zero_eq (a : Fin 13) :
    shiftedNuclearPositionQ a ⟨0,by decide⟩ =
      (((positionTable a ⟨0,by decide⟩ + 10^3 : ℤ)) : ℚ) / 10^12 := by
  simp only [shiftedNuclearPositionQ]
  rw [if_pos (show (⟨0,by decide⟩ : Fin 3) = 0 from rfl)]
  rw [nuclearPositionQ_eq_table]
  rw [show (1 : ℚ) / 10^9 = (10^3 : ℚ) / 10^12 by norm_num]
  rw [← add_div]
  push_cast
  ring

/-- The first primitive of basis `0`, used as the shift counterexample. -/
private def firstTerm : SourceGaussianModel.Term :=
  (sourceTerms (0 : Basis)).get ⟨0,by decide⟩

private def shiftedOff : Bool :=
  (List.finRange 13).all fun a =>
    decide (((firstTerm.centre ⟨0,by decide⟩).den : ℤ) <
      |(firstTerm.centre ⟨0,by decide⟩).num * (10^12 : ℤ) -
        (positionTable a ⟨0,by decide⟩ + 10^3) *
          ((firstTerm.centre ⟨0,by decide⟩).den : ℤ)|)

private theorem shiftedOff_true : shiftedOff = true := by
  decide +kernel

theorem shifted_centres_off_nuclei :
    ¬ ∀ b : Basis, ∀ t ∈ sourceTerms b,
      ∃ a : Fin 13, ∀ k : Fin 3,
        |t.centre k - shiftedNuclearPositionQ a k| ≤ (1 : ℚ) / 10^12 := by
  intro h
  have hmem : firstTerm ∈ sourceTerms (0 : Basis) := List.get_mem _ _
  obtain ⟨a,ha⟩ := h 0 firstTerm hmem
  have k0 := ha ⟨0,by decide⟩
  rw [shifted_zero_eq] at k0
  have h' := k0
  rw [← Rat.num_div_den (firstTerm.centre ⟨0,by decide⟩)] at h'
  have hint :=
    (centre_close_iff (Rat.den_ne_zero (firstTerm.centre ⟨0,by decide⟩))).mpr h'
  have hall := List.all_eq_true.mp shiftedOff_true a (List.mem_finRange _)
  have hgt := of_decide_eq_true hall
  exact absurd hint (not_le_of_gt hgt)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
