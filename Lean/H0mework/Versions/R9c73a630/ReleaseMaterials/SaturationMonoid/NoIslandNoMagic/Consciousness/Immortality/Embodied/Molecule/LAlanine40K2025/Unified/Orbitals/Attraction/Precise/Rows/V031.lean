import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_031_044
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_044_053
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_053_065
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_065_078
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_078_089
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031_089_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_31 (j : Basis) (ordered : (31 : Basis) ≤ j) :
    |aoIntegral (31 : Basis) j - (recordedAttraction (31 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (31 : Basis) = ⟨31,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(31 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(31 : Basis) ≤ (30 : Basis) by decide) ordered)
  · convert vcell31_31_error using 1; norm_num
  · convert vcell31_32_error using 1; norm_num
  · convert vcell31_33_error using 1; norm_num
  · convert vcell31_34_error using 1; norm_num
  · convert vcell31_35_error using 1; norm_num
  · convert vcell31_36_error using 1; norm_num
  · convert vcell31_37_error using 1; norm_num
  · convert vcell31_38_error using 1; norm_num
  · convert vcell31_39_error using 1; norm_num
  · convert vcell31_40_error using 1; norm_num
  · convert vcell31_41_error using 1; norm_num
  · convert vcell31_42_error using 1; norm_num
  · convert vcell31_43_error using 1; norm_num
  · convert vcell31_44_error using 1; norm_num
  · convert vcell31_45_error using 1; norm_num
  · convert vcell31_46_error using 1; norm_num
  · convert vcell31_47_error using 1; norm_num
  · convert vcell31_48_error using 1; norm_num
  · convert vcell31_49_error using 1; norm_num
  · convert vcell31_50_error using 1; norm_num
  · convert vcell31_51_error using 1; norm_num
  · convert vcell31_52_error using 1; norm_num
  · convert vcell31_53_error using 1; norm_num
  · convert vcell31_54_error using 1; norm_num
  · convert vcell31_55_error using 1; norm_num
  · convert vcell31_56_error using 1; norm_num
  · convert vcell31_57_error using 1; norm_num
  · convert vcell31_58_error using 1; norm_num
  · convert vcell31_59_error using 1; norm_num
  · convert vcell31_60_error using 1; norm_num
  · convert vcell31_61_error using 1; norm_num
  · convert vcell31_62_error using 1; norm_num
  · convert vcell31_63_error using 1; norm_num
  · convert vcell31_64_error using 1; norm_num
  · convert vcell31_65_error using 1; norm_num
  · convert vcell31_66_error using 1; norm_num
  · convert vcell31_67_error using 1; norm_num
  · convert vcell31_68_error using 1; norm_num
  · convert vcell31_69_error using 1; norm_num
  · convert vcell31_70_error using 1; norm_num
  · convert vcell31_71_error using 1; norm_num
  · convert vcell31_72_error using 1; norm_num
  · convert vcell31_73_error using 1; norm_num
  · convert vcell31_74_error using 1; norm_num
  · convert vcell31_75_error using 1; norm_num
  · convert vcell31_76_error using 1; norm_num
  · convert vcell31_77_error using 1; norm_num
  · convert vcell31_78_error using 1; norm_num
  · convert vcell31_79_error using 1; norm_num
  · convert vcell31_80_error using 1; norm_num
  · convert vcell31_81_error using 1; norm_num
  · convert vcell31_82_error using 1; norm_num
  · convert vcell31_83_error using 1; norm_num
  · convert vcell31_84_error using 1; norm_num
  · convert vcell31_85_error using 1; norm_num
  · convert vcell31_86_error using 1; norm_num
  · convert vcell31_87_error using 1; norm_num
  · convert vcell31_88_error using 1; norm_num
  · convert vcell31_89_error using 1; norm_num
  · convert vcell31_90_error using 1; norm_num
  · convert vcell31_91_error using 1; norm_num
  · convert vcell31_92_error using 1; norm_num
  · convert vcell31_93_error using 1; norm_num
  · convert vcell31_94_error using 1; norm_num
  · convert vcell31_95_error using 1; norm_num
  · convert vcell31_96_error using 1; norm_num
  · convert vcell31_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
