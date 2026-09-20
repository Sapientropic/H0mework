import H0mework.Physics.LowEnergyMatterSpace.Duhamel

/-! A source force history generates its bounded preparation map by the original Duhamel integral. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
noncomputable section

def preparationOrbit (force : ℝ → MatterFiber →L[ℂ] MatterL2) (t : ℝ) (u : MatterFiber) : MatterL2 :=
  duhamel (fun s => force s u) t

theorem preparationForce_continuous (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (u : MatterFiber) : Continuous (fun s => force s u) :=
  (ContinuousLinearMap.apply ℂ MatterL2 u).continuous.comp continuousForce

def preparationBound (force : ℝ → MatterFiber →L[ℂ] MatterL2) (t : ℝ) : ℝ :=
  |∫ s in (0 : ℝ)..t, ‖force s‖|

theorem preparationOrbit_add (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (u v : MatterFiber) :
    preparationOrbit force t (u+v)=preparationOrbit force t u+preparationOrbit force t v := by
  have integrable (w : MatterFiber) :
      IntervalIntegrable (fun s => spatialUnitary (-s) (force s w)) volume 0 t := by
    exact (interactionForcing_continuous (fun s => force s w)
      (preparationForce_continuous force continuousForce w)).intervalIntegrable (μ := volume) 0 t
  simp only [preparationOrbit,duhamel,interactionIntegral,interactionForcing,map_add]
  rw [intervalIntegral.integral_add (integrable u) (integrable v),map_add]

theorem preparationOrbit_smul (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (t : ℝ) (c : ℂ) (u : MatterFiber) :
    preparationOrbit force t (c • u)=c • preparationOrbit force t u := by
  simp only [preparationOrbit,duhamel,interactionIntegral,interactionForcing,map_smul]
  rw [intervalIntegral.integral_smul,map_smul]

theorem preparationOrbit_bound (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (u : MatterFiber) :
    ‖preparationOrbit force t u‖≤preparationBound force t*‖u‖ := by
  rw [preparationOrbit,duhamel,spatialUnitary_norm,interactionIntegral]
  have bound : ∀ᵐ s ∂volume.restrict (Set.uIoc 0 t),
      ‖interactionForcing (fun r => force r u) s‖≤‖force s‖*‖u‖ := ae_of_all _ fun s => by
    rw [interactionForcing,spatialUnitary_norm]
    exact (force s).le_opNorm u
  have integrable := (continuousForce.norm.mul_const ‖u‖).intervalIntegrable (μ := volume) 0 t
  have generated := intervalIntegral.norm_integral_le_abs_of_norm_le bound integrable
  simpa only [intervalIntegral.integral_mul_const,abs_mul,abs_of_nonneg (norm_nonneg u),preparationBound]
    using generated

def preparationLinear (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterFiber →ₗ[ℂ] MatterL2 where
  toFun := preparationOrbit force t
  map_add' := preparationOrbit_add force continuousForce t
  map_smul' := preparationOrbit_smul force t

def preparationMap (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterFiber →L[ℂ] MatterL2 :=
  (preparationLinear force continuousForce t).mkContinuous (preparationBound force t)
    (preparationOrbit_bound force continuousForce t)

theorem preparationMap_apply (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (u : MatterFiber) :
    preparationMap force continuousForce t u=duhamel (fun s => force s u) t := rfl

theorem preparationMap_norm (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) :
    ‖preparationMap force continuousForce t‖≤preparationBound force t :=
  (preparationLinear force continuousForce t).mkContinuous_norm_le (abs_nonneg _)
    (preparationOrbit_bound force continuousForce t)

theorem preparationMap_integral (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (u : MatterFiber) :
    preparationMap force continuousForce t u=
      ∫ s in (0 : ℝ)..t, spatialUnitary (t-s) (force s u) :=
  duhamel_retarded_integral _ (preparationForce_continuous force continuousForce u) t

theorem preparationMap_zero_past (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (zeroPast : ∀ s, s≤0 → force s=0) (t : ℝ) (past : t≤0) :
    preparationMap force continuousForce t=0 := by
  apply ContinuousLinearMap.ext
  intro u
  exact duhamel_zero_past (fun s => force s u) (fun s hs => by rw [zeroPast s hs]; rfl) t past

theorem preparationMap_nonzero_some_time (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (u : MatterFiber) (atTime : ℝ)
    (nonzero : force atTime u≠0) :
    ∃ t, preparationMap force continuousForce t u≠0 := by
  by_contra none
  have vanishes (t : ℝ) : duhamel (fun s => force s u) t=0 := by
    exact not_ne_iff.mp (not_exists.mp none t)
  have generated := duhamel_interaction_derivative (fun s => force s u)
    (preparationForce_continuous force continuousForce u) atTime
  have zeroOrbit : (fun s => spatialUnitary (-s) (duhamel (fun r => force r u) s))=
      (fun _ => (0 : MatterL2)) := by
    funext s
    rw [vanishes,map_zero]
  rw [zeroOrbit] at generated
  have same : spatialUnitary (-atTime) (force atTime u)=0 :=
    generated.unique (hasDerivAt_const atTime (0 : MatterL2))
  apply nonzero
  exact (spatialUnitary (-atTime)).injective (same.trans (map_zero (spatialUnitary (-atTime))).symm)

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

def controlHistory (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (t : ℝ) : MatterFiber →L[ℂ] MatterL2 :=
  (coefficient.compLpL₂ 2 volume).flip (profile t)

theorem controlHistory_apply (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (t : ℝ) (u : MatterFiber) :
    controlHistory coefficient profile t u=sourceInjection (coefficient u) (profile t) := rfl

theorem controlHistory_continuous (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (continuousProfile : Continuous profile) :
    Continuous (controlHistory coefficient profile) :=
  (coefficient.compLpL₂ 2 volume).flip.continuous.comp continuousProfile

theorem controlHistory_ae (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (t : ℝ) (u : MatterFiber) :
    controlHistory coefficient profile t u=ᵐ[volume] fun x => coefficient u (profile t x) :=
  sourceInjection_ae (coefficient u) (profile t)

def controlledPreparationMap (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (continuousProfile : Continuous profile) (t : ℝ) :
    MatterFiber →L[ℂ] MatterL2 :=
  preparationMap (controlHistory coefficient profile)
    (controlHistory_continuous coefficient profile continuousProfile) t

theorem controlledPreparationMap_duhamel (coefficient : MatterFiber →L[ℂ] C →L[ℂ] MatterFiber)
    (profile : ℝ → Lp (α := Position) C 2 volume) (continuousProfile : Continuous profile)
    (t : ℝ) (u : MatterFiber) :
    controlledPreparationMap coefficient profile continuousProfile t u=
      duhamel (fun s => sourceInjection (coefficient u) (profile s)) t := rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
