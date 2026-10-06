import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerAssemblyFeed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralAdmission
open PreparationVacuumCentralBudget PreparationVacuumPrincipalBudget PreparationVacuumReciprocalBudget
open PreparationVacuumLowerClassical
open scoped BigOperators

abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound
def Nonnegative (A : ArrayBound) : Prop := ∀ m,0 ≤ A m
def Dominates (A B : ArrayBound) : Prop := ∀ m,A m ≤ B m

theorem constant_nonnegative (c : ℝ) (hc : 0 ≤ c) : Nonnegative (constantArray c) :=
  constantArray_nonnegative c hc

theorem affine_nonnegative (v d : ℝ) (hv : 0 ≤ v) (hd : 0 ≤ d) : Nonnegative (affineArray v d) :=
  affineArray_nonnegative v d hv hd

theorem add_nonnegative (A B : ArrayBound) (ha : Nonnegative A) (hb : Nonnegative B) :
    Nonnegative (fun m => A m+B m) := fun m => _root_.add_nonneg (ha m) (hb m)

theorem scale_nonnegative (c : ℝ) (hc : 0 ≤ c) (A : ArrayBound) (ha : Nonnegative A) :
    Nonnegative (fun m => c*A m) := fun m => mul_nonneg hc (ha m)

theorem product_nonnegative (A B : ArrayBound) (ha : Nonnegative A) (hb : Nonnegative B) :
    Nonnegative (productArray A B) := productArray_nonnegative A B ha hb

theorem power_nonnegative (A : ArrayBound) (ha : Nonnegative A) (p : ℕ) :
    Nonnegative (powerArray A p) := powerArray_nonnegative A ha p

theorem constant_mono (a b : ℝ) (h : a ≤ b) : Dominates (constantArray a) (constantArray b) := by
  intro m
  by_cases hm : m=0 <;> simp [constantArray,hm,h]

theorem affine_mono (a b c d : ℝ) (h0 : a ≤ b) (h1 : c ≤ d) :
    Dominates (affineArray a c) (affineArray b d) := by
  intro m
  cases m with
  | zero => exact h0
  | succ m => cases m with
    | zero => exact h1
    | succ m => exact le_rfl

theorem add_mono (A B C D : ArrayBound) (hab : Dominates A B) (hcd : Dominates C D) :
    Dominates (fun m => A m+C m) (fun m => B m+D m) := fun m => add_le_add (hab m) (hcd m)

theorem scale_mono (c : ℝ) (hc : 0 ≤ c) (A B : ArrayBound) (hab : Dominates A B) :
    Dominates (fun m => c*A m) (fun m => c*B m) := fun m => mul_le_mul_of_nonneg_left (hab m) hc

theorem product_mono (A B C D : ArrayBound) (ha : Nonnegative A) (hc : Nonnegative C)
    (hab : Dominates A B) (hcd : Dominates C D) : Dominates (productArray A C) (productArray B D) := by
  intro m
  apply Finset.sum_le_sum
  intro k _
  have h := mul_le_mul (hab k) (hcd (m-k)) (hc _) ((ha k).trans (hab k))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (m.choose k))

theorem power_mono (A B : ArrayBound) (ha : Nonnegative A) (hab : Dominates A B) (p : ℕ) :
    Dominates (powerArray A p) (powerArray B p) := by
  induction p with
  | zero => exact fun _ => le_rfl
  | succ p ih => exact product_mono _ _ _ _ (power_nonnegative A ha p) ha ih hab

theorem inverse_mono (A B : ArrayBound) (a b : ℝ) (ha : Nonnegative A) (ha0 : 0 ≤ a)
    (hab : Dominates A B) (h0 : a ≤ b) : Dominates (inverseBudget A a) (inverseBudget B b) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => exact h0
    | succ n =>
      rw [inverseBudget_succ,inverseBudget_succ]
      apply mul_le_mul h0
      · apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hab _) (Nat.cast_nonneg _))
          (ih (n-r.val) (by omega))
          (inverseBudget_nonnegative A a ha0 ha _)
          (mul_nonneg (Nat.cast_nonneg _) ((ha _).trans (hab _)))
      · exact Finset.sum_nonneg (fun r _ => mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (ha _)) (inverseBudget_nonnegative A a ha0 ha _))
      · exact ha0.trans h0

-- The original entrywise ceiling norm of R is4, even though the actual
-- source embedding has the sharper L1 estimates used in LowerClassical.
def literalSigma : ArrayBound := fun m => 4*affineArray 915 1 m
def literalPhi : ArrayBound := fun m => literalSigma m+constantArray 4 m

theorem literalSigma_affine : literalSigma=affineArray 3660 4 := by
  funext m
  cases m with
  | zero => norm_num [literalSigma,affineArray]
  | succ m => cases m <;> norm_num [literalSigma,affineArray]

theorem literalPhi_affine : literalPhi=affineArray 3664 4 := by
  funext m
  cases m with
  | zero => norm_num [literalPhi,literalSigma,affineArray,constantArray]
  | succ m => cases m <;> norm_num [literalPhi,literalSigma,affineArray,constantArray]

theorem literalSigma_nonnegative : Nonnegative literalSigma := by
  rw [literalSigma_affine]
  exact affine_nonnegative _ _ (by norm_num) (by norm_num)

theorem literalPhi_nonnegative : Nonnegative literalPhi := by
  rw [literalPhi_affine]
  exact affine_nonnegative _ _ (by norm_num) (by norm_num)

theorem source_sigma_admission : Dominates sigmaArray literalSigma := by
  rw [literalSigma_affine]
  exact affine_mono _ _ _ _ (by norm_num) (by norm_num)

theorem source_phi_admission : Dominates phiArray literalPhi := by
  rw [literalPhi_affine]
  exact affine_mono _ _ _ _ (by norm_num) (by norm_num)

def literalUi : ArrayBound := fun m => 12*productArray AentryArray literalPhi m

theorem source_Ui_admission : Dominates UiArray literalUi := by
  apply scale_mono 12 (by norm_num)
  exact product_mono _ _ _ _ (affine_nonnegative 15 1 (by norm_num) (by norm_num))
    (affine_nonnegative 919 1 (by norm_num) (by norm_num)) (fun _ => le_rfl) source_phi_admission

theorem literalUi_nonnegative : Nonnegative literalUi :=
  scale_nonnegative 12 (by norm_num) _ (product_nonnegative _ _
    (affine_nonnegative 15 1 (by norm_num) (by norm_num)) literalPhi_nonnegative)

end LowEnergy.PreparationVacuumLiteralAdmission
