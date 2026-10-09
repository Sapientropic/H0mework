import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V045_045_079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V045_079_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_45 (j : Basis) (ordered : (45 : Basis) ≤ j) :
    |aoIntegral (45 : Basis) j - (recordedAttraction (45 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (45 : Basis) = ⟨45,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(45 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (30 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (31 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (32 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (33 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (34 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (35 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (36 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (37 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (38 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (39 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (40 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (41 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (42 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (43 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(45 : Basis) ≤ (44 : Basis) by decide) ordered)
  · convert vcell45_45_error using 1; norm_num
  · convert vcell45_46_error using 1; norm_num
  · convert vcell45_47_error using 1; norm_num
  · convert vcell45_48_error using 1; norm_num
  · convert vcell45_49_error using 1; norm_num
  · convert vcell45_50_error using 1; norm_num
  · convert vcell45_51_error using 1; norm_num
  · convert vcell45_52_error using 1; norm_num
  · convert vcell45_53_error using 1; norm_num
  · convert vcell45_54_error using 1; norm_num
  · convert vcell45_55_error using 1; norm_num
  · convert vcell45_56_error using 1; norm_num
  · convert vcell45_57_error using 1; norm_num
  · convert vcell45_58_error using 1; norm_num
  · convert vcell45_59_error using 1; norm_num
  · convert vcell45_60_error using 1; norm_num
  · convert vcell45_61_error using 1; norm_num
  · convert vcell45_62_error using 1; norm_num
  · convert vcell45_63_error using 1; norm_num
  · convert vcell45_64_error using 1; norm_num
  · convert vcell45_65_error using 1; norm_num
  · convert vcell45_66_error using 1; norm_num
  · convert vcell45_67_error using 1; norm_num
  · convert vcell45_68_error using 1; norm_num
  · convert vcell45_69_error using 1; norm_num
  · convert vcell45_70_error using 1; norm_num
  · convert vcell45_71_error using 1; norm_num
  · convert vcell45_72_error using 1; norm_num
  · convert vcell45_73_error using 1; norm_num
  · convert vcell45_74_error using 1; norm_num
  · convert vcell45_75_error using 1; norm_num
  · convert vcell45_76_error using 1; norm_num
  · convert vcell45_77_error using 1; norm_num
  · convert vcell45_78_error using 1; norm_num
  · convert vcell45_79_error using 1; norm_num
  · convert vcell45_80_error using 1; norm_num
  · convert vcell45_81_error using 1; norm_num
  · convert vcell45_82_error using 1; norm_num
  · convert vcell45_83_error using 1; norm_num
  · convert vcell45_84_error using 1; norm_num
  · convert vcell45_85_error using 1; norm_num
  · convert vcell45_86_error using 1; norm_num
  · convert vcell45_87_error using 1; norm_num
  · convert vcell45_88_error using 1; norm_num
  · convert vcell45_89_error using 1; norm_num
  · convert vcell45_90_error using 1; norm_num
  · convert vcell45_91_error using 1; norm_num
  · convert vcell45_92_error using 1; norm_num
  · convert vcell45_93_error using 1; norm_num
  · convert vcell45_94_error using 1; norm_num
  · convert vcell45_95_error using 1; norm_num
  · convert vcell45_96_error using 1; norm_num
  · convert vcell45_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
