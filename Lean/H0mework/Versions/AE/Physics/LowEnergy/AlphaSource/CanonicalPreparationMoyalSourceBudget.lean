import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalCanonicalBudget
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothActual

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumEngineSource
open scoped BigOperators ContDiff Topology

theorem originalLeaf_pole_smooth (d : Fin 3) (j : Fin 14) :
    ContDiffOn ℝ ∞ (originalLeaf d j) poleDomain :=
  fun x hx => (originalLeaf_smooth d j x hx.1.1).contDiffWithinAt

/-- Reads finite-order estimates of the actual source leaves into the original Moyal DAG budget. -/
theorem sourceScalarJordan_budget (r m : ℕ) (d e : Fin 3) (j k : Fin 14)
    (v : Word m) (x : Phase) (hx : x∈poleDomain) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ n,0≤ B n)
    (left : LeafJetBound (originalLeaf d j) (r+m) B x)
    (right : LeafJetBound (originalLeaf e k) (r+m) D x) :
    |jet m (scalarJordan r (originalLeaf d j) (originalLeaf e k)) v x|≤
      ((100 : ℝ)^r/(r.factorial : ℝ))*
        (∑ a ∈ Finset.range (m+1),(m.choose a : ℝ)*B (r+a)*D (r+(m-a))) :=
  scalarJordan_canonical_budget poleDomain_open r m (originalLeaf d j) (originalLeaf e k)
    (originalLeaf_pole_smooth d j) (originalLeaf_pole_smooth e k) v x hx B D nonnegativeB left right

def angularPair (r : ℕ) (P Q : AngularPolynomial) (target u w : AngularExponent) : Symbol :=
  if u+w=target then scalarJordan r (MvPolynomial.coeff u P) (MvPolynomial.coeff w Q) else 0

theorem weighted_coefficient (r : ℕ) (P Q : AngularPolynomial) (target : AngularExponent) :
    MvPolynomial.coeff target (weighted r P Q)=
      fun x => ∑ u∈P.support,∑ w∈Q.support,angularPair r P Q target u w x := by
  classical
  unfold weighted
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  funext x
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  by_cases same : u+w=target <;> simp [angularPair,same]

theorem weighted_coefficient_budget {U : Set Phase} (openU : IsOpen U) (r m : ℕ)
    (P Q : AngularPolynomial) (target : AngularExponent) (v : Word m) (x : Phase) (hx : x∈U)
    (B D : AngularExponent → ℕ → ℝ)
    (smoothP : ∀ u∈P.support,ContDiffOn ℝ ∞ (MvPolynomial.coeff u P) U)
    (smoothQ : ∀ w∈Q.support,ContDiffOn ℝ ∞ (MvPolynomial.coeff w Q) U)
    (nonnegativeB : ∀ u∈P.support,∀ n,0≤ B u n)
    (boundP : ∀ u∈P.support,LeafJetBound (MvPolynomial.coeff u P) (r+m) (B u) x)
    (boundQ : ∀ w∈Q.support,LeafJetBound (MvPolynomial.coeff w Q) (r+m) (D w) x) :
    |jet m (MvPolynomial.coeff target (weighted r P Q)) v x|≤
      ∑ u∈P.support,∑ w∈Q.support,
        if u+w=target then moyalScale r*convolution m r (B u) (D w) else 0 := by
  classical
  have pairSmooth (u : AngularExponent) (hu : u∈P.support) (w : AngularExponent) (hw : w∈Q.support) :
      ContDiffOn ℝ ∞ (angularPair r P Q target u w) U := by
    by_cases same : u+w=target
    · simpa only [angularPair,if_pos same] using scalarJordan_smooth openU r _ _ (smoothP u hu) (smoothQ w hw)
    · simp only [angularPair,if_neg same]
      exact contDiffOn_const
  have pairBound (u : AngularExponent) (hu : u∈P.support) (w : AngularExponent) (hw : w∈Q.support) :
      |jet m (angularPair r P Q target u w) v x|≤
        if u+w=target then moyalScale r*convolution m r (B u) (D w) else 0 := by
    by_cases same : u+w=target
    · simp only [angularPair,if_pos same]
      exact scalarJordan_canonical_budget openU r m _ _ (smoothP u hu) (smoothQ w hw)
        v x hx (B u) (D w) (nonnegativeB u hu) (boundP u hu) (boundQ w hw)
    · simp only [angularPair,if_neg same]
      simp [jet]
  rw [weighted_coefficient,jet_sum openU P.support _ (fun u hu =>
    ContDiffOn.sum (fun w hw => pairSmooth u hu w hw)) m v x hx]
  calc
    _≤∑ u∈P.support,|jet m (fun y => ∑ w∈Q.support,angularPair r P Q target u w y) v x| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤_ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [jet_sum openU Q.support _ (fun w hw => pairSmooth u hu w hw) m v x hx]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun w hw => pairBound u hu w hw))

theorem sourceWeighted_monomial_budget (r m : ℕ) (u w : AngularExponent)
    (d e : Fin 3) (j k : Fin 14) (v : Word m) (x : Phase) (hx : x∈poleDomain) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ n,0≤ B n)
    (left : LeafJetBound (originalLeaf d j) (r+m) B x)
    (right : LeafJetBound (originalLeaf e k) (r+m) D x) :
    |jet m (MvPolynomial.coeff (u+w) (weighted r
      (MvPolynomial.monomial u (originalLeaf d j)) (MvPolynomial.monomial w (originalLeaf e k)))) v x|≤
      moyalScale r*convolution m r B D := by
  rw [weighted_monomial,MvPolynomial.coeff_monomial]
  simpa only [moyalScale,convolution,ite_true] using sourceScalarJordan_budget r m d e j k v x hx B D nonnegativeB left right

theorem sourceWeighted_constants_budget (r m : ℕ)
    (d e : Fin 3) (j k : Fin 14) (v : Word m) (x : Phase) (hx : x∈poleDomain) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ n,0≤ B n)
    (left : LeafJetBound (originalLeaf d j) (r+m) B x)
    (right : LeafJetBound (originalLeaf e k) (r+m) D x) :
    |jet m (MvPolynomial.coeff 0 (weighted r (MvPolynomial.C (originalLeaf d j))
      (MvPolynomial.C (originalLeaf e k)))) v x|≤ moyalScale r*convolution m r B D := by
  rw [weighted_constants,MvPolynomial.coeff_C]
  simpa only [moyalScale,convolution,ite_true] using sourceScalarJordan_budget r m d e j k v x hx B D nonnegativeB left right

theorem source_Y_budget (r m : ℕ) (d e : Fin 3) (k : Fin 14) (v : Word m) (x : Phase) :
    jet m (scalarJordan r (originalLeaf d (Fin.last 13)) (originalLeaf e k)) v x=0 := by
  rw [originalLeaf_Y_zero]
  change jet m (scalarJordan r 0 _) v x=0
  rw [scalarJordan_zero_left]
  simp [jet]

theorem actual_energy_Moyal_budget (r m k l : ℕ) (v : Word m) (x : Phase) (hx : x∈poleDomain)
    (B D : ℕ → ℝ) (nonnegativeB : ∀ n,0≤ B n)
    (left : LeafJetBound (sourceEngineEnergy k) (r+m) B x)
    (right : LeafJetBound (sourceEngineEnergy l) (r+m) D x) :
    |jet m (scalarJordan r (sourceEngineEnergy k) (sourceEngineEnergy l)) v x|≤
      moyalScale r*convolution m r B D :=
  scalarJordan_canonical_budget poleDomain_open r m _ _
    (PreparationVacuumEngineSmooth.sourceEngineEnergy_smooth k)
    (PreparationVacuumEngineSmooth.sourceEngineEnergy_smooth l) v x hx B D nonnegativeB left right

theorem actual_clock_Moyal_budget (r m k l : ℕ) (a b : Fin 4) (i : Fin (k+1)) (j : Fin (l+1))
    (v : Word m) (x : Phase) (hx : x∈poleDomain) (B D : ℕ → ℝ) (nonnegativeB : ∀ n,0≤ B n)
    (left : LeafJetBound (sourceEngine k a i) (r+m) B x)
    (right : LeafJetBound (sourceEngine l b j) (r+m) D x) :
    |jet m (scalarJordan r (sourceEngine k a i) (sourceEngine l b j)) v x|≤
      moyalScale r*convolution m r B D :=
  scalarJordan_canonical_budget poleDomain_open r m _ _
    (PreparationVacuumEngineSmooth.sourceEngine_smooth k a i)
    (PreparationVacuumEngineSmooth.sourceEngine_smooth l b j) v x hx B D nonnegativeB left right

end LowEnergy.PreparationVacuumMoyalBudget
