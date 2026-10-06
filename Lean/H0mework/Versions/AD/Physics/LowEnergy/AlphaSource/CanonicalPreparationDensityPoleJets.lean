import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityActualHalfLog

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationScalarCoordinates
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := Phase → ℝ

def positionCoordinate (i : Fin 100) : Phase →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def inversePower (i : Fin 100) (a : ℕ) : Symbol := fun x => ((positionCoordinate i x)⁻¹)^a

def poleArray (a m : ℕ) : ℝ := (a.ascFactorial m : ℝ)*15^(a+m)

def poleDomainAt (i : Fin 100) : Set Phase := {x | positionCoordinate i x≠0}

theorem poleDomainAt_open (i : Fin 100) : IsOpen (poleDomainAt i) :=
  isOpen_ne.preimage (positionCoordinate i).continuous

theorem coordinate_pullback (i : Fin 100) (x : Phase) :
    coordinate i (fullCoordinates.symm x.1)=positionCoordinate i x := by
  simp [coordinate,positionCoordinate]

theorem positionCoordinate_direction (i : Fin 100) (s : Slot) :
    positionCoordinate i (slotDirection s)=if (i,false)=s then 1 else 0 := by
  rcases s with ⟨j,b⟩
  cases b <;> simp [positionCoordinate,slotDirection,pDirection,qDirection,Pi.single_apply]

theorem inversePower_smooth (i : Fin 100) (a : ℕ) (x : Phase) (hx : x∈poleDomainAt i) :
    ContDiffAt ℝ ∞ (inversePower i a) x := ((positionCoordinate i).contDiff.contDiffAt.inv hx).pow a

theorem inversePower_direction (i : Fin 100) (a : ℕ) (s : Slot) (x : Phase) (hx : x∈poleDomainAt i) :
    fderiv ℝ (inversePower i a) x (slotDirection s)=
      (-(a : ℝ)*(if (i,false)=s then 1 else 0))*inversePower i (a+1) x := by
  have factor := (PreparationVacuumCoframeBudget.factor_derivative true a (positionCoordinate i x)
    (fun _ _ => hx)).comp_hasFDerivAt x (positionCoordinate i).hasFDerivAt
  change HasFDerivAt (inversePower i a) _ x at factor
  rw [factor.fderiv]
  simp only [smul_apply,smul_eq_mul,positionCoordinate_direction,
    PreparationVacuumCoframeBudget.factorSlope,if_true,inversePower]
  ring

private theorem canonical_succ (f : Symbol) (m : ℕ) (w : Word (m+1)) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) :
    jet (m+1) f w x=jet m (fun y => fderiv ℝ f y (slotDirection (w (Fin.last m)))) (Fin.init w) x :=
  PreparationVacuumCoframeBudget.jet_succ_right f m w x smooth

private theorem canonical_germ {f g : Symbol} {x : Phase} (same : f=ᶠ[𝓝 x]g) (m : ℕ) (w : Word m) :
    jet m f w x=jet m g w x := PreparationVacuumCoframeBudget.jet_germ same m w

private theorem canonical_scale (c : ℝ) (f : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) : jet m (fun y => c*f y) w x=c*jet m f w x :=
  PreparationVacuumCoframeBudget.jet_scale c f m w x smooth

/-- Each repeated coordinate hit differentiates the same pole; every other hit is exactly zero. -/
theorem inversePower_jet (i : Fin 100) (a m : ℕ) (w : Word m) (x : Phase) (hx : x∈poleDomainAt i) :
    jet m (inversePower i a) w x=
      (-1 : ℝ)^m*(a.ascFactorial m : ℝ)*((positionCoordinate i x)⁻¹)^(a+m)*
        ∏ k : Fin m,(if (i,false)=w k then (1 : ℝ) else 0) := by
  induction m generalizing a with
  | zero => simp [jet,inversePower]
  | succ m ih =>
    rw [canonical_succ _ m w x (inversePower_smooth i a x hx)]
    have germ : (fun y => fderiv ℝ (inversePower i a) y (slotDirection (w (Fin.last m))))=ᶠ[𝓝 x]
        (fun y => (-(a : ℝ)*(if (i,false)=w (Fin.last m) then 1 else 0))*inversePower i (a+1) y) := by
      filter_upwards [(poleDomainAt_open i).mem_nhds hx] with y hy
      exact inversePower_direction i a _ y hy
    rw [canonical_germ germ,
      canonical_scale _ _ _ _ _ (inversePower_smooth i (a+1) x hx),ih]
    have factor : (a : ℝ)*((a+1).ascFactorial m : ℝ)=(a.ascFactorial (m+1) : ℝ) := by
      rw [←Nat.cast_mul,Nat.succ_ascFactorial,←Nat.ascFactorial_succ]
    rw [←factor,pow_succ (-1 : ℝ),Fin.prod_univ_castSucc]
    have exponent : a+1+m=a+(m+1) := by omega
    rw [exponent]
    simp only [Fin.init]
    ring

theorem inversePower_budget (i : Fin 100) (a m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈poleDomainAt i) (bound : |(positionCoordinate i x)⁻¹| ≤ 15) :
    |jet m (inversePower i a) w x| ≤ poleArray a m := by
  rw [inversePower_jet i a m w x hx]
  have indicators : |∏ k : Fin m,(if (i,false)=w k then (1 : ℝ) else 0)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intro k _; exact abs_nonneg _
    · intro k _; split_ifs <;> norm_num
  have powers := pow_le_pow_left₀ (abs_nonneg _) bound (a+m)
  rw [abs_mul,abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (Nat.cast_nonneg (a.ascFactorial m)),abs_pow]
  have head := mul_le_mul_of_nonneg_left powers (Nat.cast_nonneg (a.ascFactorial m))
  exact (mul_le_mul head indicators (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

def selectedPole (i : Fin 100) : Prop := i=0 ∨ i=2 ∨ i=5 ∨ i=67 ∨ i=77

/-- The original five chart poles are bounded on the original closed source box. -/
theorem source_pole_floor (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (i : Fin 100) (selected : selectedPole i) : (1/15 : ℝ) ≤ positionCoordinate i x := by
  have near := (abs_le.mp (box i)).1
  have sqrtLower : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_nonneg (2 : ℝ)]
  have center : (1/4 : ℝ) ≤ flatSource i := by
    rcases selected with rfl|rfl|rfl|rfl|rfl <;> norm_num [flatSource,Fin.ext_iff]
    all_goals linarith
  change (1/15 : ℝ) ≤ x.1 i
  linarith [radius_small.2]

theorem source_pole_inverse (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (i : Fin 100) (selected : selectedPole i) :
    x∈poleDomainAt i ∧ |(positionCoordinate i x)⁻¹| ≤ 15 := by
  have lower := source_pole_floor x box i selected
  have positive : 0<positionCoordinate i x := by linarith
  refine ⟨positive.ne',?_⟩
  rw [abs_of_pos (inv_pos.mpr positive)]
  have reciprocal := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/15) lower
  simpa using reciprocal

def inverseArray (m : ℕ) : ℝ := (m.factorial : ℝ)*15^(m+1)
def inverseSquareArray (m : ℕ) : ℝ := ((m+1).factorial : ℝ)*15^(m+2)

theorem actual_inverse_pole_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (i : Fin 100) (selected : selectedPole i) (m : ℕ) (w : Word m) :
    |jet m (inversePower i 1) w x| ≤ inverseArray m := by
  obtain ⟨hx,bound⟩ := source_pole_inverse x box i selected
  simpa [poleArray,inverseArray,Nat.one_ascFactorial,Nat.add_comm] using inversePower_budget i 1 m w x hx bound

theorem actual_inverse_square_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (i : Fin 100) (selected : selectedPole i) (m : ℕ) (w : Word m) :
    |jet m (inversePower i 2) w x| ≤ inverseSquareArray m := by
  obtain ⟨hx,bound⟩ := source_pole_inverse x box i selected
  have rising : (2 : ℕ).ascFactorial m=(m+1).factorial := by
    simpa only [Nat.factorial_one,one_mul,Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 m
  simpa [poleArray,inverseSquareArray,rising,Nat.add_comm] using inversePower_budget i 2 m w x hx bound

theorem inversePower_jet_zero (i : Fin 100) (a m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈poleDomainAt i) (miss : ∃ k : Fin m,w k≠(i,false)) : jet m (inversePower i a) w x=0 := by
  rw [inversePower_jet]
  obtain ⟨k,hk⟩ := miss
  have zero : (∏ k : Fin m,(if (i,false)=w k then (1 : ℝ) else 0))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (by simp [Ne.symm hk])
  rw [zero,mul_zero]
  exact hx

end LowEnergy.PreparationVacuumDensityBudget
