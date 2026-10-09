import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

namespace Mass

/-- Per-species residue-sum molar masses, exact.  The gRNA (kayjayguran,
100 nt) residue-sum mass is exactly 33040.00 Da; the mRNA (abengcemeran,
5113 nt) residue-sum mass is exactly 1656536.53 Da.  These are sums over the
printed average-mass table only; end-group chemistry is a typed residual not
included here, and no public direction or magnitude is claimed. -/
theorem residue_sum_masses :
    Source.guideResidueSumUd = 33040000000 ∧
    Source.mrnaResidueSumUd = 1656536530000 ∧
    Source.guideResidueSumGPerMol = 33040 ∧
    Source.mrnaResidueSumGPerMol = 165653653/100 ∧
    Source.residueAUd = 329210000 ∧ Source.residueCUd = 305180000 ∧
    Source.residueGUd = 345210000 ∧ Source.residueUUd = 306170000 ∧
    Source.omethylAUd = 343240000 ∧ Source.omethylCUd = 319210000 ∧
    Source.omethylGUd = 359230000 ∧ Source.omethylUUd = 320190000 ∧
    Source.methylationDeltaUd = 14030000 ∧
    Source.phosphorothioateDeltaUd = 16070000 ∧
    Source.m1psiResidueUd = 320200000 ∧
    Source.avogadroPerMol = 602214076 * 10 ^ 15 := by
  decide +kernel

/-- The N1-methylpseudouridine residue is derived exactly as printed:
pseudouridine is isomeric with uridine (printed uridine residue) plus the
printed average methylation delta (+14.03 Da). -/
theorem m1psi_derivation :
    Source.m1psiResidueUd = Source.residueUUd + Source.methylationDeltaUd := by
  decide +kernel

/-- The gRNA is the lighter species: the residue-sum mass order is strict. -/
theorem mass_order :
    (Source.guideResidueSumGPerMol : ℚ) < Source.mrnaResidueSumGPerMol ∧
    (33040 : ℚ) < 165653653/100 := by
  decide +kernel

end Mass

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
