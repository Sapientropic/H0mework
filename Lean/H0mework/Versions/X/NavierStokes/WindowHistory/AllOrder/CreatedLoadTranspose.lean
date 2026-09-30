import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.FirstResponse

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadTranspose
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistorySpatialWords (history)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created load)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (bath annihilation)
open NativeWindowHistoryOseen (action)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

private theorem dissipative_cross {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (sign : ∀u,inner ℝ u (A u) ≤ 0) (x y : E) (d : ℝ) (d0 : 0<d) :
    |inner ℝ (A y) x+inner ℝ y (A x)| ≤ -d*inner ℝ x (A x)-d⁻¹*inner ℝ y (A y) := by
  have first:=sign (d • x+y)
  have last:=sign (d • x-y)
  simp only [map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right] at first last
  have swapped:=real_inner_comm x (A y)
  have cancel : d*(-d*inner ℝ x (A x)-d⁻¹*inner ℝ y (A y))=
      -d^2*inner ℝ x (A x)-inner ℝ y (A y) := by field_simp
  apply abs_le.mpr
  constructor <;> nlinarith only [first,last,cancel,swapped,d0]

def cross (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (x y : H) : ℝ :=
  inner ℝ (action seed M t y) x+inner ℝ y (action seed M t x)

private theorem scaled_cross (n e gx gy : ℝ) (n0 : 0<n) (e0 : 0<e) :
    2*(-(e/(2*n))*(-n*gx)-(e/(2*n))⁻¹*(-n*gy))=e*gx+(4*n^2/e)*gy := by
  field_simp
  ring

set_option backward.isDefEq.respectTransparency false in
theorem cross_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (x y : H)
    (epsilon : ℝ) (positive : 0<epsilon) :
    2*|cross seed M t x y| ≤ epsilon*gradient M x+(4*nu.coeff^2/epsilon)*gradient M y := by
  let d:=epsilon/(2*nu.coeff)
  have d0 : 0<d:=div_pos positive (by positivity [nu.coeff_pos])
  have paid:=dissipative_cross (E := H) (action seed M t) (NativeWindowHistoryOseen.action_dissipative seed M t) x y d d0
  have read:=congrArg₂ (fun p q : ℝ => -d*p-d⁻¹*q)
    (NativeWindowHistoryOseenGap.action_energy seed M t x) (NativeWindowHistoryOseenGap.action_energy seed M t y)
  exact (mul_le_mul_of_nonneg_left (paid.trans_eq read) (by norm_num : (0:ℝ) ≤ 2)).trans_eq
    (scaled_cross nu.coeff epsilon (gradient M x) (gradient M y) nu.coeff_pos positive)

private theorem rescale (n w p g : ℝ) (n0 : 0<n)
    (paid : 2*n⁻¹*w ≤ (n⁻¹)^2*p+g) : 2*w ≤ n⁻¹*p+n*g := by
  have multiplied:=mul_le_mul_of_nonneg_left paid n0.le
  have first : n*(2*n⁻¹*w)=2*w := by field_simp
  have last : n*((n⁻¹)^2*p+g)=n⁻¹*p+n*g := by field_simp
  rwa [first,last] at multiplied

def inputBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  NativeWindowHistoryCreationHalf.budget seed horizon*NativeWindowHistoryCreationFirstJet.budget seed 0 horizon

theorem inputBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ inputBudget seed horizon :=
  mul_nonneg (NativeWindowHistoryCreationHalf.budget_nonnegative seed horizon)
    (NativeWindowHistoryCreationFirstJet.budget_nonnegative seed 0 horizon)

theorem creation_pair_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (j : Coordinate)
    (t : ℝ) (inside : t∈Icc 0 horizon) (r : H) (delta : ℝ) (positive : 0<delta) :
    |2*inner ℝ (creation seed M t (value seed M [j] t)) r| ≤
      delta*gradient M r+delta⁻¹*inputBudget seed horizon := by
  let v:=NativeWindowHistoryCreationFirstJet.firstJet seed M 0 j t
  have p:NativeWindowHistorySchurWeakPairing.potential seed M t v ≤ inputBudget seed horizon :=
    (NativeWindowHistoryCreationHalf.potential_bound seed horizon M t inside v).trans
      (mul_le_mul_of_nonneg_left (NativeWindowHistoryCreationFirstJet.firstJet_bound seed 0 horizon M j t inside)
        (NativeWindowHistoryCreationHalf.budget_nonnegative seed horizon))
  have read:=NativeWindowHistoryCreationFirstJet.source_original seed M j t
  have bound (a : ℝ) : 2*a*inner ℝ (creation seed M t (value seed M [j] t)) r ≤
      a^2*inputBudget seed horizon+gradient M r := by
    have source:=NativeWindowHistorySchurWeakPairing.creation_young seed M t v r a
    rw [read] at source
    exact source.trans (add_le_add (mul_le_mul_of_nonneg_left p (sq_nonneg a)) (le_refl _))
  have upper:=rescale delta _ _ _ positive (bound delta⁻¹)
  have negative : 2*delta⁻¹*(-inner ℝ (creation seed M t (value seed M [j] t)) r) ≤
      (delta⁻¹)^2*inputBudget seed horizon+gradient M r := by
    simpa only [neg_sq,mul_neg,neg_mul] using bound (-delta⁻¹)
  have lower:=rescale delta _ _ _ positive negative
  exact abs_le.mpr ⟨by linarith only [lower],by linarith only [upper]⟩

def pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) : ℝ :=
  2*inner ℝ (created seed M word a B aB t) (history seed M word t)

def transpose (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) : ℝ :=
  2*cross seed M t (history seed M word t) (created seed M word a B aB t)+
    2*inner ℝ (creation seed M t (value seed M word t)) (created seed M word a B aB t)+
    2*inner ℝ (creation seed M t (value seed M word t)) (history seed M word t)

private theorem compressed_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P A : E →L[ℝ] E) (symmetric : ∀u v,inner ℝ (P u) v=inner ℝ u (P v))
    (x y p : E) (centered : P y=y) (projection : P x=x-p) :
    inner ℝ (P (A (P y))) x=inner ℝ (A y) x-inner ℝ (A y) p := by
  rw [symmetric,centered,projection,inner_sub_right]

set_option backward.isDefEq.respectTransparency false in
theorem bath_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc a B) :
    inner ℝ (bath seed M t (created seed M word a B aB t)) (history seed M word t)=
      inner ℝ (action seed M t (created seed M word a B aB t)) (history seed M word t)+
        inner ℝ (creation seed M t (value seed M word t)) (created seed M word a B aB t) := by
  let x:=history seed M word t
  let y:=created seed M word a B aB t
  let v:=value seed M word t
  have centered : Q y=y:=NativeWindowHistoryCausalCreationEnergy.centered seed M (value seed M word)
    (NativeWindowHistoryAllOrderCausal.value_continuous seed M word) a B aB t inside
  have projection : Q x=x-embed v := by
    change x-embed (mean x)=x-embed v
    rw [← NativeWindowHistoryAllOrderWord.value_original]
  have first:=compressed_pair (E := H) Q (action seed M t) NativeWindowHistoryMeanProjection.residual_symmetric
    x y (embed v) centered projection
  have annih:=(NativeWindowHistoryMeanBlocks.annihilation_pairing seed M t v y).trans
    (congrArg (fun z : H => inner ℝ (embed v) (action seed M t z)) centered)
  have swap:=real_inner_comm (action seed M t y) (embed v)
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M t v y
  change inner ℝ (bath seed M t y) x=_ at first
  linarith only [first,annih,swap,green]

set_option backward.isDefEq.respectTransparency false in
theorem pairing_hasDerivWithinAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (pairing seed M word a B aB)
      (2*inner ℝ (created seed M word a B aB t) (load seed M word t)+transpose seed M word a B aB t) (Icc a B) t := by
  have yd:=NativeWindowHistoryAllOrderCausal.created_derivative seed M word a B aB t inside
  have xd : HasDerivWithinAt (history seed M word)
      (action seed M t (history seed M word t)+load seed M word t) (Icc a B) t :=
    ((NativeWindowHistorySpatialWords.source_action seed M word t).congr_deriv (add_assoc _ _ _)).hasDerivWithinAt
  have actual:=(yd.inner ℝ xd).const_mul 2
  apply actual.congr_deriv
  simp only [inner_add_left,inner_add_right]
  rw [bath_pair seed M word a B aB t inside]
  dsimp only [transpose,cross]
  ring

theorem transpose_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (j : Coordinate) (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc 0 horizon) :
    |transpose seed M [j] a B aB t| ≤ epsilon*gradient M (history seed M [j] t)+
      (8*nu.coeff^2/epsilon+1)*gradient M (created seed M [j] a B aB t)+
        (1+2/epsilon)*inputBudget seed horizon := by
  let x:=history seed M [j] t
  let y:=created seed M [j] a B aB t
  have first:=cross_bound seed M t x y (epsilon/2) (by positivity)
  have last:=creation_pair_bound seed horizon M j t inside x (epsilon/2) (by positivity)
  have middle:=creation_pair_bound seed horizon M j t inside y 1 (by norm_num)
  have triangle := (abs_add_le (2*cross seed M t x y+2*inner ℝ (creation seed M t (value seed M [j] t)) y)
    (2*inner ℝ (creation seed M t (value seed M [j] t)) x)).trans
    (add_le_add (abs_add_le _ _) (le_refl _))
  have scale : |2*cross seed M t x y|=2*|cross seed M t x y| := by rw [abs_mul]; norm_num
  rw [scale] at triangle
  have arithmetic : 4*nu.coeff^2/(epsilon/2)=8*nu.coeff^2/epsilon := by ring
  have inverse : (epsilon/2)⁻¹=2/epsilon := by field_simp
  rw [arithmetic] at first
  rw [inverse] at last
  norm_num only [one_mul,inv_one] at middle
  exact triangle.trans ((add_le_add (add_le_add first middle) last).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadTranspose
