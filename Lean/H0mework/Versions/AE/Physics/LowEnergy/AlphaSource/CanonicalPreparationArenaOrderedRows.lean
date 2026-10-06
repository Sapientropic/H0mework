import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaMoyal
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCentralCoefficients

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaRows
open PreparationVacuumArenaBudget PreparationVacuumCanonicalMoyal PreparationVacuumMoyalBudget
open PreparationVacuumCentralBudget PreparationVacuumClockSymbol
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := ℕ → ℝ
abbrev SmoothComplex (f : ComplexSymbol) := ContDiffOn ℝ ∞ f poleDomain

def orderedProduct (fs : List ComplexSymbol) : ComplexSymbol :=
  fun x=>fs.foldr (fun f out=>f x*out) 1

def orderedArray (bs : List ArrayBound) : ArrayBound :=
  bs.foldr productArray (constantArray 1)

theorem complex_finite_product (f g : ComplexSymbol) (hf : SmoothComplex f) (hg : SmoothComplex g)
    (B D : ArrayBound) (nonnegativeB : ∀ m,0≤B m) (N : ℕ)
    (x : Phase) (hx : x∈poleDomain) (left : ComplexJetBound f N B x)
    (right : ComplexJetBound g N D x) :
    ComplexJetBound (fun y=>f y*g y) N (productArray B D) x := by
  intro m hm w
  have lists := complexListJet_product_bound poleDomain_open f g hf hg
    (List.ofFn (slotDirection∘w)) x hx 0 B D nonnegativeB
    (by
      intro s hs
      have lengths:=wordSplittings_lengths (List.ofFn (slotDirection∘w)) s hs
      have can:=(split_canonical _ (canonical_ofFn w) s hs).1
      simpa only [zero_add] using complex_canonical_list_bound poleDomain_open f hf N B x hx
        left s.1 can (by simp only [List.length_ofFn] at lengths;omega))
    (by
      intro s hs
      have lengths:=wordSplittings_lengths (List.ofFn (slotDirection∘w)) s hs
      have can:=(split_canonical _ (canonical_ofFn w) s hs).2
      simpa only [zero_add] using complex_canonical_list_bound poleDomain_open g hg N D x hx
        right s.2 can (by simp only [List.length_ofFn] at lengths;omega))
  rw [complexListJet_ofFn poleDomain_open (hf.mul hg) m (slotDirection∘w) x hx] at lists
  simpa only [List.length_ofFn,convolution,zero_add,productArray] using lists

theorem orderedProduct_smooth (fs : List ComplexSymbol)
    (smooth : ∀ f∈fs,SmoothComplex f) : SmoothComplex (orderedProduct fs) := by
  induction fs with
  | nil=>exact contDiffOn_const
  | cons f fs ih=>
    exact (smooth f (by simp)).mul (ih (fun g hg=>smooth g (by simp [hg])))

theorem orderedArray_nonnegative (bs : List ArrayBound)
    (positive : ∀ B∈bs,∀ m,0≤B m) : ∀ m,0≤orderedArray bs m := by
  induction bs with
  | nil=>exact constantArray_nonnegative 1 (by norm_num)
  | cons B bs ih=>
    exact productArray_nonnegative B (orderedArray bs) (positive B (by simp))
      (ih (fun D hd=>positive D (by simp [hd])))

theorem complex_finite_constant (c : ℂ) (N : ℕ) (x : Phase) :
    ComplexJetBound (fun _=>c) N (constantArray ‖c‖) x := by
  intro m _ w
  cases m with
  | zero=>simp [constantArray]
  | succ m=>simp [constantArray,iteratedFDeriv_succ_const]

theorem orderedProduct_budget {ι : Type} (xs : List ι) (f : ι → ComplexSymbol)
    (B : ι → ArrayBound) (smooth : ∀ i∈xs,SmoothComplex (f i))
    (positive : ∀ i∈xs,∀ m,0≤B i m) (N : ℕ) (x : Phase) (hx : x∈poleDomain)
    (bounds : ∀ i∈xs,ComplexJetBound (f i) N (B i) x) :
    ComplexJetBound (orderedProduct (xs.map f)) N (orderedArray (xs.map B)) x := by
  induction xs with
  | nil=>
    change ComplexJetBound (fun _=>1) N (constantArray 1) x
    simpa only [norm_one] using complex_finite_constant 1 N x
  | cons i xs ih=>
    apply complex_finite_product (f i) (orderedProduct (xs.map f)) (smooth i (by simp))
      (orderedProduct_smooth _ (by
        intro g hg
        obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hg
        exact smooth j (by simp [hj]))) (B i) (orderedArray (xs.map B))
      (positive i (by simp)) N x hx (bounds i (by simp))
      (ih (fun j hj=>smooth j (by simp [hj])) (fun j hj=>positive j (by simp [hj]))
        (fun j hj=>bounds j (by simp [hj])))

end LowEnergy.PreparationVacuumArenaRows
