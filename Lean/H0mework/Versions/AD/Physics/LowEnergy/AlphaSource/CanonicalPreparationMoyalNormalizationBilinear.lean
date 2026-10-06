import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaSourceNormalization

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalNormalization
open PreparationVacuumDAGSemantic PreparationVacuumArenaBudget PreparationVacuumArenaRows
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

theorem moyal_add_left (r : ℕ) (f g h : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (hh : SmoothComplex h)
    (x : Phase) (hx : x∈poleDomain) :
    complexMoyal r (fun y=>f y+g y) h x=complexMoyal r f h x+complexMoyal r g h x := by
  rw [←complexCoefficient_arena poleDomain_open r _ _ (hf.add hg) hh x hx,
    ←complexCoefficient_arena poleDomain_open r _ _ hf hh x hx,
    ←complexCoefficient_arena poleDomain_open r _ _ hg hh x hx]
  unfold complexCoefficient complexContraction
  simp only [complexListJet_add poleDomain_open f g hf hg _ hx]
  simp only [mul_add,add_mul,Finset.sum_add_distrib]

theorem moyal_scale_left (r : ℕ) (c : ℂ) (f g : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (x : Phase) (hx : x∈poleDomain) :
    complexMoyal r (fun y=>c*f y) g x=c*complexMoyal r f g x := by
  rw [←complexCoefficient_arena poleDomain_open r _ _ (contDiffOn_const.mul hf) hg x hx,
    ←complexCoefficient_arena poleDomain_open r _ _ hf hg x hx]
  unfold complexCoefficient complexContraction
  simp only [complexListJet_scale poleDomain_open c f hf _ hx]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem moyal_add_right (r : ℕ) (f g h : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (hh : SmoothComplex h)
    (x : Phase) (hx : x∈poleDomain) :
    complexMoyal r f (fun y=>g y+h y) x=complexMoyal r f g x+complexMoyal r f h x := by
  rw [complexMoyal_swap r _ f,moyal_add_left r g h f hg hh hf x hx]
  rw [complexMoyal_swap r g f,complexMoyal_swap r h f]
  ring

theorem moyal_scale_right (r : ℕ) (c : ℂ) (f g : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (x : Phase) (hx : x∈poleDomain) :
    complexMoyal r f (fun y=>c*g y) x=c*complexMoyal r f g x := by
  rw [complexMoyal_swap r _ f,moyal_scale_left r c g f hg hf x hx,
    complexMoyal_swap r g f]
  ring

theorem moyal_zero_left (r : ℕ) (f : Phase→ℂ) (x : Phase) :
    complexMoyal r (fun _=>0) f x=0 := by
  simp [complexMoyal,coefficient_zero_left]

theorem moyal_zero_right (r : ℕ) (f : Phase→ℂ) (x : Phase) :
    complexMoyal r f (fun _=>0) x=0 := by
  rw [complexMoyal_swap,moyal_zero_left,mul_zero]

theorem arena_add_left {k : ℕ} (r : ℕ) (e f g : ArenaExpression k) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.moyal r (.add e f) g) x=
      arenaEvaluate (.add (.moyal r e g) (.moyal r f g)) x :=
  moyal_add_left r _ _ _ (arena_smooth e) (arena_smooth f) (arena_smooth g) x hx

theorem arena_add_right {k : ℕ} (r : ℕ) (e f g : ArenaExpression k) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.moyal r e (.add f g)) x=
      arenaEvaluate (.add (.moyal r e f) (.moyal r e g)) x :=
  moyal_add_right r _ _ _ (arena_smooth e) (arena_smooth f) (arena_smooth g) x hx

theorem arena_numeric_left {k : ℕ} (r : ℕ) (c : ℝ) (e f : ArenaExpression k)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.moyal r (arenaProduct (.literal c) e) f) x=
      arenaEvaluate (arenaProduct (.literal c) (.moyal r e f)) x := by
  have value : arenaEvaluate (arenaProduct (.literal c) e)=(fun y=>(c:ℂ)*arenaEvaluate e y) :=
    funext (fun y=>arenaProduct_evaluate _ _ y)
  rw [arenaEvaluate_moyal,value,arenaProduct_evaluate]
  exact moyal_scale_left r c _ _ (arena_smooth e) (arena_smooth f) x hx

theorem arena_numeric_right {k : ℕ} (r : ℕ) (c : ℝ) (e f : ArenaExpression k)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.moyal r e (arenaProduct (.literal c) f)) x=
      arenaEvaluate (arenaProduct (.literal c) (.moyal r e f)) x := by
  have value : arenaEvaluate (arenaProduct (.literal c) f)=(fun y=>(c:ℂ)*arenaEvaluate f y) :=
    funext (fun y=>arenaProduct_evaluate _ _ y)
  rw [arenaEvaluate_moyal,value,arenaProduct_evaluate]
  exact moyal_scale_right r c _ _ (arena_smooth e) (arena_smooth f) x hx

end LowEnergy.PreparationVacuumMoyalNormalization
