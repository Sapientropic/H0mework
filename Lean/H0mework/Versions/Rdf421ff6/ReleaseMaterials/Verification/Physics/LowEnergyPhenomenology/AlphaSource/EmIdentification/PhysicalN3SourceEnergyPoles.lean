import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3SourceInverseRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedVisiblePoleOwn.ActualDressedRationalVisiblePole

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open Polynomial
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open scoped InnerProductSpace

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator

/-- The reduced rational form of the actual N3 detector energy read: the same scalar
numerator over the original joint source polynomial, reduced by the generic pole calculus. -/
abbrev physicalN3InputEnergyFraction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) : RatFunc ℂ :=
  readFraction (physicalN3InputEnergyNumerator p F leg) (jointPolynomial p F)

/-- The visible source energy poles of the actual read: roots of the reduced denominator. -/
abbrev physicalN3EnergyPoles (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) : Multiset ℂ :=
  visibleRoots (physicalN3InputEnergyFraction p F leg)

/-- The reduced denominator is nonzero. -/
theorem physical_n3_fraction_denom_nonzero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    (physicalN3InputEnergyFraction p F leg).denom≠0:=
  RatFunc.denom_ne_zero _

/-- The reduced numerator is nonzero: the source read is not the zero fraction. -/
theorem physical_n3_fraction_num_nonzero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    (physicalN3InputEnergyFraction p F leg).num≠0:=by
  have qne : (jointPolynomial p F)≠0:=(jointPolynomial_monic p F).ne_zero
  have cross :=reduced_cross_identity (physicalN3InputEnergyNumerator p F leg)
    (jointPolynomial p F) qne
  intro zero
  rw [zero,zero_mul] at cross
  have product : (physicalN3InputEnergyNumerator p F leg)*
      (physicalN3InputEnergyFraction p F leg).denom=0:=cross.symm
  rw [mul_eq_zero] at product
  exact product.elim (physical_n3_numerator_nonzero p F leg)
    (physical_n3_fraction_denom_nonzero p F leg)

/-- The reduced denominator has positive degree: the `d↦d-1` strict drop leaves room for at
least one source pole. -/
theorem physical_n3_denom_degree_positive (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    0<(physicalN3InputEnergyFraction p F leg).denom.natDegree:=by
  have qne : (jointPolynomial p F)≠0:=(jointPolynomial_monic p F).ne_zero
  have nnum :=physical_n3_fraction_num_nonzero p F leg
  have dne :=physical_n3_fraction_denom_nonzero p F leg
  have p'ne :=physical_n3_numerator_nonzero p F leg
  have cross :=reduced_cross_identity (physicalN3InputEnergyNumerator p F leg)
    (jointPolynomial p F) qne
  have degs :=congrArg Polynomial.natDegree cross
  rw [natDegree_mul nnum qne,natDegree_mul p'ne dne,
    physical_n3_numerator_degree] at degs
  have qpos :=physical_n3_joint_degree_positive p F
  omega

/-- The visible source pole packet is nonempty: algebraically closed `ℂ` plus positive
denominator degree produces at least one real-source root. -/
theorem physical_n3_energy_poles_nonempty (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    ∃a : ℂ,a∈physicalN3EnergyPoles p F leg:=by
  have dne :=physical_n3_fraction_denom_nonzero p F leg
  have pos : 0<(physicalN3InputEnergyFraction p F leg).denom.degree:=by
    rw [degree_eq_natDegree dne]
    exact_mod_cast physical_n3_denom_degree_positive p F leg
  obtain ⟨a,root⟩ :=Complex.exists_root pos
  exact ⟨a,(visible_root_iff _ a).mpr root⟩

/-- Every visible source energy pole is real: a nonreal root would contradict the original
`q.eval`-nonvanishing theorem through the denominator divisibility. -/
theorem physical_n3_energy_pole_real (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (a : ℂ) (root : a∈physicalN3EnergyPoles p F leg) :
    a.im=0:=by
  by_contra ne
  have eval :=(visible_root_iff (physicalN3InputEnergyFraction p F leg) a).mp root
  obtain ⟨r,hr⟩ :=reduced_denominator_dvd (physicalN3InputEnergyNumerator p F leg)
    (jointPolynomial p F)
  have zero : (jointPolynomial p F).eval a=0:=by
    rw [hr,eval_mul,eval,zero_mul]
  exact source_joint_polynomial_nonreal p F a ne zero

/-- Each visible source pole has positive reduced pole order. -/
theorem physical_n3_energy_pole_order_positive (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (a : ℂ)
    (root : a∈physicalN3EnergyPoles p F leg) :
    0<poleOrder (physicalN3InputEnergyFraction p F leg) a:=
  visible_pole_order_positive _ _ root

/-- Each visible source pole has nonzero canonical leading coefficient. -/
theorem physical_n3_energy_pole_leading_nonzero (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (a : ℂ)
    (root : a∈physicalN3EnergyPoles p F leg) :
    leadingPoleCoefficient (physicalN3InputEnergyFraction p F leg) a≠0:=
  leading_pole_coefficient_nonzero _ _ root

/-- The root-indexed packet of actual source energy poles. -/
abbrev N3SourceEnergyPole (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) : Type :=
  {a : ℂ // a∈physicalN3EnergyPoles p F leg}

/-- The source pole packet is inhabited. -/
noncomputable instance instNonemptyN3SourceEnergyPole (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) :
    Nonempty (N3SourceEnergyPole p F leg) :=by
  obtain ⟨a,ha⟩ :=physical_n3_energy_poles_nonempty p F leg
  exact ⟨⟨a,ha⟩⟩

/-- Weighted pole limit on the nonreal-to-real boundary curve `z = a + i·sigma` with
`sigma → 0⁺`: the actual seed-paired inverse read, scaled by the source pole order,
converges to the canonical leading coefficient. No simple-pole assumption is made; the
canonical leading coefficient is the top Laurent coefficient, which is not claimed to be
the residue when the reduced order exceeds one. -/
theorem physical_n3_energy_pole_boundary_limit (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) :
    Filter.Tendsto
      (fun sigma : ℝ =>
        ((↑pole.val+Complex.I*(sigma:ℂ)-↑pole.val)^
          poleOrder (physicalN3InputEnergyFraction p F leg) pole.val)*
          physicalN3InputEnergyRead p F leg (↑pole.val+Complex.I*(sigma:ℂ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (leadingPoleCoefficient (physicalN3InputEnergyFraction p F leg) pole.val)):=by
  have curve : Filter.Tendsto (fun sigma : ℝ => ↑pole.val+Complex.I*(sigma:ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin ↑pole.val ({↑pole.val}ᶜ)):=by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have cont : Continuous (fun sigma : ℝ => ↑pole.val+Complex.I*(sigma:ℂ)):=
        continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      have tendsto : Filter.Tendsto (fun sigma : ℝ => ↑pole.val+Complex.I*(sigma:ℂ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ↑pole.val):=by
        simpa using (cont.tendsto 0).mono_left nhdsWithin_le_nhds
      exact tendsto
    · filter_upwards [self_mem_nhdsWithin] with sigma hpos
      have pos : 0<sigma:=Set.mem_Ioi.mp hpos
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      intro eq
      have him :=congrArg Complex.im eq
      simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul] at him
      linarith
  have limit :=(pole_order_limit (physicalN3InputEnergyFraction p F leg) pole.val).comp curve
  apply Filter.Tendsto.congr' _ limit
  filter_upwards [self_mem_nhdsWithin] with sigma hpos
  have pos : 0<sigma:=Set.mem_Ioi.mp hpos
  have zim : (↑pole.val+Complex.I*(sigma:ℂ)).im=sigma:=by
    simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add,
      physical_n3_energy_pole_real p F leg pole.val pole.property]
  have nonreal : (↑pole.val+Complex.I*(sigma:ℂ)).im≠0:=by
    rw [zim]
    exact ne_of_gt pos
  have reg :=source_joint_polynomial_nonreal p F _ nonreal
  simp only [Function.comp_apply]
  rw [reduced_read_at_regular _ _ _ reg,physical_n3_read_eq_eval p F leg _ nonreal]

/-- Generic unit-resolvent pairing continuity on an abstract Hilbert space: wherever a
spectral affine pencil `T - z·1` meets a unit, the `Ring.inverse` pairing read is
continuous. No concrete `H` normalization is needed. -/
private theorem n3_unit_inverse_read {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E→L[ℂ]E) (x : E) (a : ℂ)
    (u : (E→L[ℂ]E)ˣ) (hu : T-a•(1 : E→L[ℂ]E)=u) :
    ContinuousAt (fun z : ℂ => inner ℂ x ((Ring.inverse (T - z•(1 : E→L[ℂ]E))) x)) a:=by
  have pencil : ContinuousAt (fun z : ℂ => T - z•(1 : E→L[ℂ]E)) a:=
    (continuous_const.sub (continuous_id.smul continuous_const)).continuousAt
  have inverse : ContinuousAt (Ring.inverse : (E→L[ℂ]E)→(E→L[ℂ]E))
      (T - a•(1 : E→L[ℂ]E)):=hu.symm ▸ (contDiffAt_ringInverse ℂ (n:=1) u).continuousAt
  have applied : ContinuousAt
      (fun z : ℂ => (Ring.inverse (T - z•(1 : E→L[ℂ]E))) x) a:=
    ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt).comp
      (Filter.Tendsto.comp inverse pencil)
  exact (continuous_inner).continuousAt.comp (continuousAt_const.prodMk applied)

/-- Generic pole singularity on an abstract Hilbert space: if the weighted inverse
pairing `(z - a)^m · ⟪x, (T - z·1)⁻¹ x⟫` tends to a nonzero value `L` along the real
boundary curve `z = a + i·σ`, then `T - a·1` cannot be a unit. All operator algebra and
unit witnesses stay on `E`, so no concrete `H` normalization is triggered inside. -/
private theorem n3_pole_singularity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E→L[ℂ]E) (x : E) (a : ℂ)
    (m : ℕ) (L : ℂ) (mpos : 0 < m) (Lne : L≠0)
    (hlimit : Filter.Tendsto
      (fun sigma : ℝ => (a+Complex.I*(sigma:ℂ)-a)^m*
        inner ℂ x ((Ring.inverse (T-(a+Complex.I*(sigma:ℂ))•(1 : E→L[ℂ]E))) x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ¬IsUnit (T-a•(1 : E→L[ℂ]E)):=by
  intro unit
  obtain ⟨u,hu⟩ :=unit
  have readCont :=n3_unit_inverse_read T x a u hu.symm
  have curve : Filter.Tendsto (fun sigma : ℝ => a+Complex.I*(sigma:ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a):=by
    have cont : Continuous (fun sigma : ℝ => a+Complex.I*(sigma:ℂ)):=
      continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
    simpa using (cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have readLim :=Filter.Tendsto.comp readCont curve
  have base : Filter.Tendsto (fun sigma : ℝ => a+Complex.I*(sigma:ℂ)-a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0):=by
    have cont : Continuous (fun sigma : ℝ => a+Complex.I*(sigma:ℂ)-a):=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).sub
        continuous_const
    simpa using (cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have pow0 : (0:ℂ)^m=0:=zero_pow mpos.ne'
  have powlim : Filter.Tendsto (fun sigma : ℝ => (a+Complex.I*(sigma:ℂ)-a)^m)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0):=by
    simpa only [pow0] using base.pow m
  have prod : Filter.Tendsto
      (fun sigma : ℝ => (a+Complex.I*(sigma:ℂ)-a)^m*
        inner ℂ x ((Ring.inverse (T-(a+Complex.I*(sigma:ℂ))•(1 : E→L[ℂ]E))) x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0):=by
    simpa only [Function.comp_apply,zero_mul] using powlim.mul readLim
  exact Lne (tendsto_nhds_unique hlimit prod)

private theorem n3_read_shift (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) :
    physicalN3InputEnergyRead p F leg z=
      inner ℂ (actualElectronPhysicalSeed leg)
        (Ring.inverse (jointGenerator p F 0 0-z • (1 : H→L[ℂ]H))
          (actualElectronPhysicalSeed leg)) := by
  have shifted :=PreparationVacuumCurrentRegularAnchor.jointGenerator_spectral_shift p F z (0:Field289)
  have inverseEq :=congrArg (fun A : H→L[ℂ]H=>Ring.inverse A) shifted
  have paired :=congrArg (fun A : H→L[ℂ]H=>
    inner ℂ (actualElectronPhysicalSeed leg) (A (actualElectronPhysicalSeed leg))) inverseEq
  calc
    physicalN3InputEnergyRead p F leg z=
        inner ℂ (actualElectronPhysicalSeed leg) (actualElectronPhysicalResponse p F z leg) :=
      physicalN3InputEnergyRead.eq_def p F leg z
    _=inner ℂ (actualElectronPhysicalSeed leg)
        (jointResolvent p F z 0 (actualElectronPhysicalSeed leg)) :=
      congrArg (inner ℂ (actualElectronPhysicalSeed leg))
        (actualElectronPhysicalResponse.eq_def p F z leg)
    _=inner ℂ (actualElectronPhysicalSeed leg)
        (Ring.inverse (jointGenerator p F z 0) (actualElectronPhysicalSeed leg)) :=
      congrArg (fun A : H→L[ℂ]H=>
        inner ℂ (actualElectronPhysicalSeed leg) (A (actualElectronPhysicalSeed leg)))
        (jointResolvent.eq_def p F z 0)
    _=_ :=paired

/-- A nonzero source pole limit rules out a unit of the original physical generator. -/
theorem physical_n3_energy_pole_singular (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) :
    ¬IsUnit (jointGenerator p F pole.val 0):=by
  have hlimit : Filter.Tendsto
      (fun sigma : ℝ=>(pole.val+Complex.I*(sigma:ℂ)-pole.val)^
        poleOrder (physicalN3InputEnergyFraction p F leg) pole.val*
        inner ℂ (actualElectronPhysicalSeed leg)
          (Ring.inverse (jointGenerator p F 0 0-
            (pole.val+Complex.I*(sigma:ℂ)) • (1:H→L[ℂ]H))
            (actualElectronPhysicalSeed leg)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (leadingPoleCoefficient (physicalN3InputEnergyFraction p F leg) pole.val)) := by
    simpa only [n3_read_shift] using physical_n3_energy_pole_boundary_limit p F leg pole
  have singular :=n3_pole_singularity (jointGenerator p F 0 0)
    (actualElectronPhysicalSeed leg) pole.val
    (poleOrder (physicalN3InputEnergyFraction p F leg) pole.val)
    (leadingPoleCoefficient (physicalN3InputEnergyFraction p F leg) pole.val)
    (physical_n3_energy_pole_order_positive p F leg pole.val pole.property)
    (physical_n3_energy_pole_leading_nonzero p F leg pole.val pole.property) hlimit
  have shifted :=PreparationVacuumCurrentRegularAnchor.jointGenerator_spectral_shift p F pole.val (0:Field289)
  exact shifted.symm ▸ singular

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
