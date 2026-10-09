import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V040_040_076
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V040_076_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_40 (j : Basis) (ordered : (40 : Basis) ≤ j) :
    |aoIntegral (40 : Basis) j - (recordedAttraction (40 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (40 : Basis) = ⟨40,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(40 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (30 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (31 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (32 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (33 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (34 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (35 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (36 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (37 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (38 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(40 : Basis) ≤ (39 : Basis) by decide) ordered)
  · convert vcell40_40_error using 1; norm_num
  · convert vcell40_41_error using 1; norm_num
  · convert vcell40_42_error using 1; norm_num
  · convert vcell40_43_error using 1; norm_num
  · convert vcell40_44_error using 1; norm_num
  · convert vcell40_45_error using 1; norm_num
  · convert vcell40_46_error using 1; norm_num
  · convert vcell40_47_error using 1; norm_num
  · convert vcell40_48_error using 1; norm_num
  · convert vcell40_49_error using 1; norm_num
  · convert vcell40_50_error using 1; norm_num
  · convert vcell40_51_error using 1; norm_num
  · convert vcell40_52_error using 1; norm_num
  · convert vcell40_53_error using 1; norm_num
  · convert vcell40_54_error using 1; norm_num
  · convert vcell40_55_error using 1; norm_num
  · convert vcell40_56_error using 1; norm_num
  · convert vcell40_57_error using 1; norm_num
  · convert vcell40_58_error using 1; norm_num
  · convert vcell40_59_error using 1; norm_num
  · convert vcell40_60_error using 1; norm_num
  · convert vcell40_61_error using 1; norm_num
  · convert vcell40_62_error using 1; norm_num
  · convert vcell40_63_error using 1; norm_num
  · convert vcell40_64_error using 1; norm_num
  · convert vcell40_65_error using 1; norm_num
  · convert vcell40_66_error using 1; norm_num
  · convert vcell40_67_error using 1; norm_num
  · convert vcell40_68_error using 1; norm_num
  · convert vcell40_69_error using 1; norm_num
  · convert vcell40_70_error using 1; norm_num
  · convert vcell40_71_error using 1; norm_num
  · convert vcell40_72_error using 1; norm_num
  · convert vcell40_73_error using 1; norm_num
  · convert vcell40_74_error using 1; norm_num
  · convert vcell40_75_error using 1; norm_num
  · convert vcell40_76_error using 1; norm_num
  · convert vcell40_77_error using 1; norm_num
  · convert vcell40_78_error using 1; norm_num
  · convert vcell40_79_error using 1; norm_num
  · convert vcell40_80_error using 1; norm_num
  · convert vcell40_81_error using 1; norm_num
  · convert vcell40_82_error using 1; norm_num
  · convert vcell40_83_error using 1; norm_num
  · convert vcell40_84_error using 1; norm_num
  · convert vcell40_85_error using 1; norm_num
  · convert vcell40_86_error using 1; norm_num
  · convert vcell40_87_error using 1; norm_num
  · convert vcell40_88_error using 1; norm_num
  · convert vcell40_89_error using 1; norm_num
  · convert vcell40_90_error using 1; norm_num
  · convert vcell40_91_error using 1; norm_num
  · convert vcell40_92_error using 1; norm_num
  · convert vcell40_93_error using 1; norm_num
  · convert vcell40_94_error using 1; norm_num
  · convert vcell40_95_error using 1; norm_num
  · convert vcell40_96_error using 1; norm_num
  · convert vcell40_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
