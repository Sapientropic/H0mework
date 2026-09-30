import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatTopology

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatEvaluation
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedSexticLatticePower NativeUnheatedTreeHeatTopology
noncomputable section

def symbol (nu : Viscosity) (p q : Wave) : ℝ :=
  factor nu*mass (p+q)^(1/2 : ℝ)/(mass p+mass q)

theorem symbol_nonnegative (nu : Viscosity) (p q : Wave) : 0 ≤ symbol nu p q := by
  unfold symbol
  positivity [factor_positive nu, mass_positive p, mass_positive q, mass_positive (p+q)]

theorem unweight_kernel (a b : ℝ) (p q : Wave) :
    mass (p+q)^(-(a+b-1/2)/2)*NativeUnheatedTreeHeatKernel.kernel a b p q =
      mass (p+q)^(1/2 : ℝ)/(mass p+mass q)*mass p^(-a/2)*mass q^(-b/2) := by
  unfold NativeUnheatedTreeHeatKernel.kernel
  calc
    _ = (mass (p+q)^(-(a+b-1/2)/2)*mass (p+q)^((a+b+1/2)/2))*
        mass p^(-a/2)*mass q^(-b/2)/(mass p+mass q) := by ring
    _ = _ := by
      rw [← Real.rpow_add (mass_positive (p+q)),
        show -(a+b-1/2)/2+(a+b+1/2)/2 = (1/2 : ℝ) by ring]
      ring

theorem envelope_term (nu : Viscosity) (left right : Tree) (small : leaves (.fork left right) ≤ 7)
    (input : E) (k p : Wave) :
    mass k^(-grade (.fork left right)/2)*factor nu*
      NativeUnheatedTreeHeatConvolution.term (grade left) (grade right)
        (value nu left (left_small left right small) input) (value nu right (right_small left right small) input) k p =
      symbol nu p (k-p)*envelope nu left (left_small left right small) input p*
        envelope nu right (right_small left right small) input (k-p) := by
  unfold NativeUnheatedTreeHeatConvolution.term envelope symbol
  rw [abs_of_nonneg (value_nonnegative nu left _ input p),
    abs_of_nonneg (value_nonnegative nu right _ input (k-p)), grade_fork]
  have paid := unweight_kernel (grade left) (grade right) p (k-p)
  rw [add_sub_cancel] at paid
  calc
    _ = factor nu*(mass k^(-(grade left+grade right-1/2)/2)*
        NativeUnheatedTreeHeatKernel.kernel (grade left) (grade right) p (k-p))*
        value nu left (left_small left right small) input p*
        value nu right (right_small left right small) input (k-p) := by ring
    _ = _ := by rw [paid, add_sub_cancel]; ring

theorem envelope_summable (nu : Viscosity) (left right : Tree) (small : leaves (.fork left right) ≤ 7)
    (input : E) (k : Wave) :
    Summable (fun p => symbol nu p (k-p)*envelope nu left (left_small left right small) input p*
      envelope nu right (right_small left right small) input (k-p)) := by
  have paid := (NativeUnheatedTreeHeatConvolution.row_summable (grade left) (grade right)
    (grade_le left) (grade_le right) (grade_total left right small)
    (value nu left (left_small left right small) input) (value nu right (right_small left right small) input) k).mul_left
      (mass k^(-grade (.fork left right)/2)*factor nu)
  exact paid.congr (envelope_term nu left right small input k)

theorem envelope_fork (nu : Viscosity) (left right : Tree) (small : leaves (.fork left right) ≤ 7)
    (input : E) (k : Wave) :
    envelope nu (.fork left right) small input k =
      ∑' p, symbol nu p (k-p)*envelope nu left (left_small left right small) input p*
        envelope nu right (right_small left right small) input (k-p) := by
  change mass k^(-grade (.fork left right)/2)*(factor nu*
    (∑' p, NativeUnheatedTreeHeatConvolution.term (grade left) (grade right)
      (value nu left (left_small left right small) input) (value nu right (right_small left right small) input) k p)) = _
  rw [← mul_assoc, ← tsum_mul_left]
  exact tsum_congr (envelope_term nu left right small input k)

def Index : Tree → Type
  | .leaf => PUnit
  | .fork left right => Wave × (Index left × Index right)

def term (nu : Viscosity) (input : E) : (tree : Tree) → Wave → Index tree → ℝ
  | .leaf, k, _ => mass k^(-(2/7 : ℝ)/2)*|input k|
  | .fork left right, k, index => symbol nu index.1 (k-index.1)*
      term nu input left index.1 index.2.1*term nu input right (k-index.1) index.2.2

theorem term_nonnegative (nu : Viscosity) (input : E) (tree : Tree) (k : Wave) (index : Index tree) :
    0 ≤ term nu input tree k index := by
  induction tree generalizing k with
  | leaf => exact mul_nonneg (Real.rpow_pos_of_pos (mass_positive k) _).le (abs_nonneg _)
  | fork left right first last =>
    exact mul_nonneg (mul_nonneg (symbol_nonnegative nu _ _) (first _ _)) (last _ _)

theorem complete_sum (nu : Viscosity) (input : E) (tree : Tree) (small : leaves tree ≤ 7) (k : Wave) :
    Summable (term nu input tree k) ∧ ∑' index, term nu input tree k index = envelope nu tree small input k := by
  induction tree generalizing k with
  | leaf =>
    have finite : Summable (term nu input Tree.leaf k) := by
      change Summable (fun _ : PUnit => mass k^(-(2/7 : ℝ)/2)*|input k|)
      exact (hasSum_fintype _).summable
    refine ⟨finite, ?_⟩
    change (∑' _ : PUnit, mass k^(-(2/7 : ℝ)/2)*|input k|) = _
    norm_num [envelope, NativeUnheatedTreeHeatTopology.grade, leaves, value, lp.toNorm]
  | fork left right first last =>
    have leftPaid (p : Wave) := first (left_small left right small) p
    have rightPaid (p : Wave) := last (right_small left right small) (k-p)
    have inner (p : Wave) : Summable (fun index : Index left × Index right =>
        symbol nu p (k-p)*term nu input left p index.1*term nu input right (k-p) index.2) := by
      exact ((leftPaid p).1.mul_left (symbol nu p (k-p))).mul_of_nonneg (rightPaid p).1
        (fun index => mul_nonneg (symbol_nonnegative nu p (k-p)) (term_nonnegative nu input left p index))
        (term_nonnegative nu input right (k-p))
    have inner_read (p : Wave) : (∑' index : Index left × Index right,
        symbol nu p (k-p)*term nu input left p index.1*term nu input right (k-p) index.2) =
        symbol nu p (k-p)*envelope nu left (left_small left right small) input p*
          envelope nu right (right_small left right small) input (k-p) := by
      rw [(inner p).tsum_prod]
      simp only [tsum_mul_left, tsum_mul_right, (leftPaid p).2, (rightPaid p).2]
    have generated : Summable (term nu input (.fork left right) k) := by
      apply (summable_prod_of_nonneg (term_nonnegative nu input (.fork left right) k)).mpr
      refine ⟨inner, ?_⟩
      change Summable (fun p => ∑' index : Index left × Index right,
        symbol nu p (k-p)*term nu input left p index.1*term nu input right (k-p) index.2)
      simp only [inner_read]
      exact envelope_summable nu left right small input k
    refine ⟨generated, ?_⟩
    change (∑' index : Wave × (Index left × Index right), term nu input (.fork left right) k index) = _
    rw [generated.tsum_prod]
    change (∑' p, ∑' index : Index left × Index right,
      symbol nu p (k-p)*term nu input left p index.1*term nu input right (k-p) index.2) = _
    simp only [inner_read]
    exact (envelope_fork nu left right small input k).symm

def rootTerm (nu : Viscosity) (input : E) (tree : Tree) (k : Wave) (index : Index tree) : ℝ :=
  (2*Real.pi)⁻¹*mass k^(-(1/2 : ℝ))*term nu input tree k index

theorem root_summable (nu : Viscosity) (input : E) (tree : Tree) (small : leaves tree ≤ 7) (k : Wave) :
    Summable (rootTerm nu input tree k) :=
  (complete_sum nu input tree small k).1.mul_left _

def rootValue (nu : Viscosity) (input : E) (tree : Tree) (seven : leaves tree = 7) : E :=
  (2*Real.pi)⁻¹ • value nu tree seven.le input

theorem rootValue_apply (nu : Viscosity) (input : E) (tree : Tree) (seven : leaves tree = 7) (k : Wave) :
    rootValue nu input tree seven k = ∑' index, rootTerm nu input tree k index := by
  have grading : NativeUnheatedTreeHeatTopology.grade tree = -1 := by
    norm_num [NativeUnheatedTreeHeatTopology.grade, seven]
  simp only [rootTerm, tsum_mul_left, (complete_sum nu input tree seven.le k).2, envelope, grading]
  change (2*Real.pi)⁻¹*value nu tree seven.le input k = _
  have powers : mass k^(-(1/2 : ℝ))*mass k^(-(-1 : ℝ)/2) = 1 := by
    rw [← Real.rpow_add (mass_positive k), show -(1/2 : ℝ)+-(-1 : ℝ)/2 = 0 by ring,
      Real.rpow_zero]
  calc
    _ = (2*Real.pi)⁻¹*(mass k^(-(1/2 : ℝ))*mass k^(-(-1 : ℝ)/2))*value nu tree seven.le input k := by rw [powers]; ring
    _ = _ := by ring

theorem rootValue_bound (nu : Viscosity) (input : E) (tree : Tree) (seven : leaves tree = 7) :
    ‖rootValue nu input tree seven‖ ≤ (2*Real.pi)⁻¹*cost nu^6*‖input‖^7 := by
  have count : nodes tree = 6 := by have paid := leaves_nodes tree; omega
  rw [rootValue, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2*Real.pi)⁻¹)]
  have paid := mul_le_mul_of_nonneg_left (value_bound nu tree seven.le input)
    (by positivity : 0 ≤ (2*Real.pi)⁻¹)
  simpa only [count, seven, mul_assoc] using paid

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatEvaluation
