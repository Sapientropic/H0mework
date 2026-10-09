import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualSignedSectorResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSignedSector
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceScalarPairedTransport FullYDynamicSource
open SourceQuantumConfigurationHilbert
open scoped InnerProductSpace Topology
attribute [local irreducible] embed

private theorem exp_preserves_input {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (C : V →L[ℂ] V) (L : V →L[ℂ] H)
    (s : ℝ) (hC : ∀ x, projection s (L x) = L x → projection s (L (C x)) = L (C x))
    (x : V) (hx : projection s (L x) = L x) (t : ℝ) :
    projection s (L (SourceFiniteUnitary.time C t x)) = L (SourceFiniteUnitary.time C t x) := by
  let A : V →L[ℂ] V := t • ((-Complex.I) • C)
  let ev : (V →L[ℂ] V) →L[ℂ] H := L.comp (ContinuousLinearMap.apply ℂ V x)
  have lr (a : ℝ) (v : V) : L (a • v) = a • L v := (L.restrictScalars ℝ).map_smul a v
  have pr (a : ℝ) (v : H) : projection s (a • v) = a • projection s v :=
    ((projection s).restrictScalars ℝ).map_smul a v
  have power (n : ℕ) : projection s (L ((A^n) x)) = L ((A^n) x) := by
    induction n with
    | zero => simpa only [pow_zero,one_apply_eq_self] using hx
    | succ n ih =>
      rw [pow_succ',mul_apply_eq_comp]
      simpa only [A,_root_.smul_apply,lr,pr,map_smul] using
        congrArg (fun v : H => t • ((-Complex.I) • v)) (hC ((A^n) x) ih)
  have series := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map ev ev.continuous
  have projected := series.map (projection s) (projection s).continuous
  have equal' (n : ℕ) : projection s (ev (((Nat.factorial n : ℂ)⁻¹) • A^n)) = ev (((Nat.factorial n : ℂ)⁻¹) • A^n) := by
    change projection s (L ((((Nat.factorial n : ℂ)⁻¹) • A^n) x)) =
      L ((((Nat.factorial n : ℂ)⁻¹) • A^n) x)
    simp only [_root_.smul_apply,map_smul,power]
  have heq : (fun n : ℕ => projection s (ev (((Nat.factorial n : ℂ)⁻¹) • A^n))) =
      (fun n : ℕ => ev (((Nat.factorial n : ℂ)⁻¹) • A^n)) := funext equal'
  change HasSum (fun n : ℕ => projection s (ev (((Nat.factorial n : ℂ)⁻¹) • A^n))) _ at projected
  rw [heq] at projected
  exact projected.unique series

/-- The original generated finite source orbit is used unchanged. Only its
actual input and generator are shown to remain in the signed source sector. -/
theorem actual_time_sector (s : ℝ) (F : Index) (q : QuantumTest)
    (hq : project s q = q) (sharp : Bool) (t : ℝ) :
    project s (literalCoreTime (saturate s F) sharp q t) = literalCoreTime (saturate s F) sharp q t := by
  let K := saturate s F
  let S := sourceSpace K sharp q
  let C := sourceGenerator K sharp q
  let x : S := sourceEquiv K sharp q ⟨q,sourceOrbit_input K sharp q⟩
  have input : (x : H) = embed q := rfl
  have hC (y : S) (hy : projection s (y : H) = (y : H)) :
      projection s (C y : H) = (C y : H) := by
    let v := ((sourceEquiv K sharp q).symm y).val
    have hv : embed v = (y : H) := congrArg Subtype.val ((sourceEquiv K sharp q).apply_symm_apply y)
    have fixed : project s v = v := by
      apply embed_injective
      rw [embed_project,hv,hy]
    have output : (C y : H) = embed ((compressionCore K+sourceY sharp) v) := rfl
    rw [output,←embed_project,actual_full_generator s F sharp,fixed]
  have hx : projection s (x : H) = (x : H) := by rw [input,←embed_project,hq]
  have he := exp_preserves_input C S.subtypeL s hC x hx t
  have out : embed (literalCoreTime K sharp q t) = (SourceFiniteUnitary.time C t x : H) :=
    congrArg Subtype.val ((sourceEquiv K sharp q).apply_symm_apply _)
  apply embed_injective
  rw [embed_project,out]
  exact he

end LowEnergy.ActualSignedSector
