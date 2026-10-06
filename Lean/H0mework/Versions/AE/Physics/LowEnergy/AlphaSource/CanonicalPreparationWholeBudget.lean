import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWholeActualJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeTail
open PreparationVacuumLocalizedTail PreparationVacuumOriginalRadii PreparationVacuumCanonicalMoyal
open PreparationVacuumConicComposition PreparationVacuumConicBudget PreparationVacuumClockSymbol
open PreparationVacuumEngineSmooth PreparationVacuumEngineBudget PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

theorem shifted_head_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ j∈Finset.range n,f (j+2))=∑ k∈Finset.Ico 2 (n+2),f k := by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [Finset.sum_range_succ,show n+1+2=(n+2)+1 by omega,Finset.sum_Ico_succ_top (by omega)]
    rw [ih]

theorem actual_whole_tail_budget (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : ∀ k,2≤k → FiniteBound (PreparationVacuumEngineSource.sourceEngineEnergy k)
      m (B k 4) (unitPhase x)) :
    |jet m (energyTailFor B) w x|≤originalTailBudget B m := by
  let K:=originalTailStart m
  let L:=nearbyHead x
  have kbound : 3≤K:=le_max_right _ _
  have count : nearbyHead x≤(K-2)+L:=by dsimp [L];omega
  rw [energyTailFor_jet_readback B m w x hx ((K-2)+L) count,Finset.sum_range_add]
  have head : (∑ j∈Finset.range (K-2),jet m (energyTailTerm B (j+2)) w x)=
      ∑ k∈Finset.Ico 2 K,jet m (energyTailTerm B k) w x := by
    have result:=shifted_head_sum (fun k=>jet m (energyTailTerm B k) w x) (K-2)
    simpa only [show K-2+2=K by omega] using result
  have tail : (∑ j∈Finset.range L,jet m (energyTailTerm B (K-2+j+2)) w x)=
      ∑ j∈Finset.range L,jet m (energyTailTerm B (K+j)) w x := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [head,tail]
  exact actual_original_finite_tail B positive m L x hx outside primitive w

theorem actual_whole_tail_finite (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N : ℕ) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : ∀ k,2≤k → FiniteBound (PreparationVacuumEngineSource.sourceEngineEnergy k)
      N (B k 4) (unitPhase x)) :
    FiniteBound (energyTailFor B) N (originalTailBudget B) x := by
  intro m hm w
  exact actual_whole_tail_budget B positive m w x hx outside
    (fun k hk n hn v=>primitive k hk n (hn.trans hm) v)

-- The full locally-finite function is consumed here; no completed-tail seminorm
-- or finite-order truncation is supplied as a target witness.
theorem actual_whole_tail_102 (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : ∀ k,2≤k → FiniteBound (PreparationVacuumEngineSource.sourceEngineEnergy k)
      102 (B k 4) (unitPhase x)) :
    FiniteBound (energyTailFor B) 102 (originalTailBudget B) x :=
  actual_whole_tail_finite B positive 102 x hx outside primitive

end LowEnergy.PreparationVacuumWholeTail
