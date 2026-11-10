import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronPhysicalChargeReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuantumBinaryReturn
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationCommonCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussHistoryHilbert
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open PreparationVacuumGradedTransport PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumFullFieldRiesz
open SourcePropagationCommonMomentum ActualCompositeFieldCurrent ActualElectronPhysicalNormalization
open PreparationVacuumNoetherResponsePrice ActualMixedNoetherTimePriceOwn
open ActualSourceMixed289ResponseOwn PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard PreparationVacuumRawJointFeedback
open Filter Set
open scoped InnerProductSpace Topology BigOperators
attribute [local irreducible] jointResolvent jointGenerator physicalAction embed coreEquiv
attribute [local irreducible] movedClosedY movedGraph movingDiagonal sourceResolvent transportedCompression compression
  actualElectronPhysicalResponse actualElectronPhysicalSeed

local instance physicalSpan_finite (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    FiniteDimensional ℂ (physicalSpan p F) :=FiniteCoreEvolution.coreSpan_finite (physical p) F

private theorem physical_span_retained (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (x : H) (inside : x∈physicalSpan p F) :x∈retainedSpace p F := by
  let A : physicalSpan p F→ₗ[ℂ]H :=(retainer p F).toLinearMap.comp (physicalSpan p F).subtype
  let B : physicalSpan p F→ₗ[ℂ]H :=(physicalSpan p F).subtype
  have equal : A=B := by
    apply (physicalBasis p F).toBasis.ext
    intro i
    exact retainer_basis p F i
  exact (retainedSpace_iff p F x).mpr (DFunLike.congr_fun equal ⟨x,inside⟩)

/-- The actual source chooses one frame event before every physical momentum; no retainer witness is supplied. -/
theorem actual_electron_physical_seed_retained_event (leg : CompositeLeg) :
    ∀ᶠF in (GaussUnitaryHistory.sourceFilter : Filter GaussUnitaryHistory.Index),
      ∀p : PhysicalMomentum,actualElectronPhysicalSeed leg∈retainedSpace p F := by
  classical
  have contains : ∀ᶠF in (GaussUnitaryHistory.sourceFilter : Filter GaussUnitaryHistory.Index),
      coreEquiv (actualElectronAmputatedLeg leg)∈F := by
    apply WeakCoreEvolution.sourceFilter_cofinal diagonal
    exact Filter.eventually_atTop.mpr ⟨{coreEquiv (actualElectronAmputatedLeg leg)},fun F larger=>
      larger (Finset.mem_singleton_self _)⟩
  filter_upwards [contains] with F inside p
  have span :=FiniteCoreEvolution.mem_coreSpan (physical 0) F (coreEquiv (actualElectronAmputatedLeg leg)) inside
  apply physical_span_retained p F (actualElectronPhysicalSeed leg)
  rw [physicalSpan_common]
  have same : ((coreEquiv (actualElectronAmputatedLeg leg)) : H)=actualElectronPhysicalSeed leg := by
    unfold coreEquiv actualElectronPhysicalSeed
    rfl
  simpa only [same] using span

/-- Original closed-Y graph return and source equation at the actual physical inverse output. -/
def actualElectronPhysicalDomainReturn (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (leg : CompositeLeg) : Prop :=
    ∃y : H,(actualElectronPhysicalResponse p F z leg,y)∈movedGraph (0:Field289) 0 ∧
        compression p F (actualElectronPhysicalResponse p F z leg)+
          y-
          z • actualElectronPhysicalResponse p F z leg=actualElectronPhysicalSeed leg

attribute [local irreducible] actualElectronPhysicalDomainReturn

private theorem physical_domain_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg)
    (kept : actualElectronPhysicalSeed leg∈retainedSpace p F) :
    actualElectronPhysicalDomainReturn p F z leg := by
  unfold actualElectronPhysicalDomainReturn actualElectronPhysicalResponse
  have nz : z≠0 := by intro zero; exact nonreal (by rw [zero]; rfl)
  have unit :=(movingDiagonal_units (0:Field289) p F z nonreal).self_of_nhds
  obtain ⟨domain,equation⟩ :=uncut_resolvent_domain (0:Field289) p F z nz 0 unit
    (actualElectronPhysicalSeed leg) kept
  let x : H:=sourceResolvent (0:Field289) p F none z 0 (actualElectronPhysicalSeed leg)
  let y : H:=movedClosedY (0:Field289) 0 ⟨x,domain⟩
  have graph : (x,y)∈movedGraph (0:Field289) 0 := by
    rw [←movedClosedY_graph]
    exact LinearPMap.mem_graph (movedClosedY (0:Field289) 0) ⟨x,domain⟩
  have compressed : compression p F x+y-z • x=actualElectronPhysicalSeed leg :=
    (congrArg (fun A : H→L[ℂ]H=>A x+y-z • x)
      (transportedCompression_zero (0:Field289) p F)).symm.trans equation
  have output : jointResolvent p F z 0 (actualElectronPhysicalSeed leg)=x :=
    congrArg (fun A : H→L[ℂ]H=>A (actualElectronPhysicalSeed leg))
      (jointResolvent_zero (0:Field289) p F z)
  refine ⟨y,?_,?_⟩
  · exact (congrArg (fun u : H=>(u,y)∈movedGraph (0:Field289) 0) output).mpr graph
  · exact (congrArg (fun u : H=>compression p F u+y-z • u) output).trans compressed

/-- The same source generates one retained-frame event for every momentum and every nonreal physical inverse. -/
theorem actual_electron_physical_uncut_domain_event (leg : CompositeLeg) :
    ∀ᶠF in (GaussUnitaryHistory.sourceFilter : Filter GaussUnitaryHistory.Index),
      ∀(p : PhysicalMomentum) (z : ℂ),z.im≠0→actualElectronPhysicalDomainReturn p F z leg := by
  exact (actual_electron_physical_seed_retained_event leg).mono
    (fun F kept p z nonreal=>physical_domain_return p F z nonreal leg (kept p))

/-- Both actual N3 external source units consume the full two-momentum inverse vertex. -/
def actualElectronPhysicalFieldVertex (g : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (left right : CompositeLeg) (h : Field289) : ℂ :=
  inner ℂ (actualElectronPhysicalSeed left) (jointVertex g p k F z w h (actualElectronPhysicalSeed right))

def actualElectronPhysicalMixedField (f g : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (left right : CompositeLeg) : ℂ :=
  inner ℂ (actualElectronPhysicalSeed left) (mixedVertex f g p k F z w (actualElectronPhysicalSeed right))

/-- Amputation returns the physical source current of the original whole-field generator, including its uncut Y variation. -/
theorem actual_electron_physical_field_amputation (g : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (nonrealLeft : z.im≠0) (nonrealRight : w.im≠0) :
    jointGenerator (p+k) F z 0*jointVertex g p k F z w 0*jointGenerator p F w 0=
      -PreparationVacuumUncutYukawa.sourceCurrent g p F none 0 := by
  unfold jointVertex
  calc
    _=-((jointGenerator (p+k) F z 0*jointResolvent (p+k) F z 0)*
      jointCurrent p F w 0 g*(jointResolvent p F w 0*jointGenerator p F w 0)) := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [mul_apply_eq_comp,neg_apply,map_neg]
    _=-((1:H→L[ℂ]H)*jointCurrent p F w 0 g*(1:H→L[ℂ]H)) :=
      congrArg₂ (fun A B : H→L[ℂ]H=>-(A*jointCurrent p F w 0 g*B))
        (actual_electron_joint_inverse_right (p+k) F z nonrealLeft)
        (actual_electron_joint_inverse_left p F w nonrealRight)
    _=-jointCurrent p F w 0 g := by simp only [one_mul,mul_one]
    _=_ := by rw [jointCurrent_source]

/-- Left/right physical generator currents and the original mixed Hessian contact are differentiated together. -/
theorem actual_electron_physical_mixed_generated (f g : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (nonrealLeft : z.im≠0) (nonrealRight : w.im≠0)
    (left right : CompositeLeg) :
    HasDerivAt (fun r : ℝ=>actualElectronPhysicalFieldVertex g p k F z w left right (r • f))
      (actualElectronPhysicalMixedField f g p k F z w left right) 0 :=
  paired_derivative (mixedVertex_generated f g p k F z w nonrealLeft nonrealRight)
    (actualElectronPhysicalSeed left) (actualElectronPhysicalSeed right)

def actualElectronPhysicalContactRead (q : PhysicalResponsePoint) (reader force : Field289)
    (age : ℝ) (left right : CompositeLeg) : ℂ :=
  inner ℂ (actualElectronPhysicalSeed left)
    ((correctedContactJet q reader force age).value (actualElectronPhysicalSeed right))

/-- The same complete two physical times, two actual joint inverses and contact-minus-raw increment act on the new physical N3 endpoints. -/
theorem actual_electron_physical_contact_price (q : PhysicalResponsePoint) (reader force : Field289)
    (age : ℝ) (leftNonreal : q.z.im≠0) (rightNonreal : q.w.im≠0) (left right : CompositeLeg) :
    ‖actualElectronPhysicalContactRead q reader force age left right‖≤
      originalPhysicalTimePrice (q.p+q.k) q.F (-age)*originalJointResolventPrice (q.p+q.k) q.F q.z*
        originalNoetherRawIncrementPrice reader force q.p q.F*originalJointResolventPrice q.p q.F q.w*
          originalPhysicalTimePrice q.p q.F age := by
  unfold actualElectronPhysicalContactRead
  calc
    _≤‖actualElectronPhysicalSeed left‖*
      ‖(correctedContactJet q reader force age).value (actualElectronPhysicalSeed right)‖ := norm_inner_le_norm _ _
    _=‖(correctedContactJet q reader force age).value (actualElectronPhysicalSeed right)‖ := by rw [actual_electron_physical_seed_norm,one_mul]
    _≤‖(correctedContactJet q reader force age).value‖*‖actualElectronPhysicalSeed right‖ :=
      (correctedContactJet q reader force age).value.le_opNorm _
    _=‖(correctedContactJet q reader force age).value‖ := by rw [actual_electron_physical_seed_norm,mul_one]
    _≤_ := original_corrected_contact_time_source_price q reader force age leftNonreal rightNonreal

/-- The original sourceFilter completes the actual physical inverse outputs, after their own source-generated normalization. -/
def actualElectronPhysicalStateFamily (p : PhysicalMomentum) (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :
    SourceFamilyHilbert.Family H GaussUnitaryHistory.sourceFilter :=
  ⟨fun F=>actualElectronPhysicalUnit p F z leg,1,zero_le_one,
    fun F=>(actual_electron_physical_unit_norm p F z nonreal leg).le⟩

def actualElectronPhysicalState (p : PhysicalMomentum) (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :
    GaussUnitaryHistory.HistorySpace :=
  (actualElectronPhysicalStateFamily p z nonreal leg : GaussUnitaryHistory.HistorySpace)

theorem actual_electron_physical_state_norm (p : PhysicalMomentum) (z : ℂ) (nonreal : z.im≠0)
    (leg : CompositeLeg) :‖actualElectronPhysicalState p z nonreal leg‖=1 := by
  have convergence :=SourceFamilyHilbert.norm_tendsto GaussUnitaryHistory.sourceFilter
    (actualElectronPhysicalStateFamily p z nonreal leg)
  simp only [actualElectronPhysicalStateFamily,SourceFamilyHilbert.value,
    actual_electron_physical_unit_norm p _ z nonreal leg] at convergence
  have norm : (1:ℝ)=‖actualElectronPhysicalStateFamily p z nonreal leg‖ :=
    tendsto_nhds_unique (tendsto_const_nhds (x:=(1:ℝ))) convergence
  rw [actualElectronPhysicalState,UniformSpace.Completion.norm_coe,←norm]

/-- The whole-carrier diagonal read is the sourceFilter limit of the actual same-frame physical output reads. -/
theorem actual_electron_physical_state_charge_return (p : PhysicalMomentum) (z : ℂ) (nonreal : z.im≠0)
    (leg : CompositeLeg) :
    Tendsto (fun F=>actualElectronPhysicalChargeRead p F z leg)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ (actualElectronPhysicalState p z nonreal leg)
        (GaussUnitaryHistory.reader (CanonicalGradedCharge.chargeReader sourcePhaseGaugeLie)
          (actualElectronPhysicalState p z nonreal leg)))) := by
  change Tendsto (fun F=>actualElectronPhysicalChargeRead p F z leg)
    GaussUnitaryHistory.sourceFilter (𝓝 (inner ℂ
      (actualElectronPhysicalStateFamily p z nonreal leg : GaussUnitaryHistory.HistorySpace)
      (SourceFamilyOperator.lift GaussUnitaryHistory.sourceFilter
        (SourceFamilyOperator.constant (CanonicalGradedCharge.chargeReader sourcePhaseGaugeLie))
        (actualElectronPhysicalStateFamily p z nonreal leg : GaussUnitaryHistory.HistorySpace))))
  rw [SourceFamilyOperator.lift_coe,SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto GaussUnitaryHistory.sourceFilter
    (actualElectronPhysicalStateFamily p z nonreal leg)
    (SourceFamilyOperator.act GaussUnitaryHistory.sourceFilter
      (SourceFamilyOperator.constant (CanonicalGradedCharge.chargeReader sourcePhaseGaugeLie))
      (actualElectronPhysicalStateFamily p z nonreal leg))

end LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse
