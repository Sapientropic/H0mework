import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V043_043_078
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V043_078_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_43 (j : Basis) (ordered : (43 : Basis) ≤ j) :
    |aoIntegral (43 : Basis) j - (recordedAttraction (43 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (43 : Basis) = ⟨43,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(43 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (30 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (31 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (32 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (33 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (34 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (35 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (36 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (37 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (38 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (39 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (40 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (41 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(43 : Basis) ≤ (42 : Basis) by decide) ordered)
  · convert vcell43_43_error using 1; norm_num
  · convert vcell43_44_error using 1; norm_num
  · convert vcell43_45_error using 1; norm_num
  · convert vcell43_46_error using 1; norm_num
  · convert vcell43_47_error using 1; norm_num
  · convert vcell43_48_error using 1; norm_num
  · convert vcell43_49_error using 1; norm_num
  · convert vcell43_50_error using 1; norm_num
  · convert vcell43_51_error using 1; norm_num
  · convert vcell43_52_error using 1; norm_num
  · convert vcell43_53_error using 1; norm_num
  · convert vcell43_54_error using 1; norm_num
  · convert vcell43_55_error using 1; norm_num
  · convert vcell43_56_error using 1; norm_num
  · convert vcell43_57_error using 1; norm_num
  · convert vcell43_58_error using 1; norm_num
  · convert vcell43_59_error using 1; norm_num
  · convert vcell43_60_error using 1; norm_num
  · convert vcell43_61_error using 1; norm_num
  · convert vcell43_62_error using 1; norm_num
  · convert vcell43_63_error using 1; norm_num
  · convert vcell43_64_error using 1; norm_num
  · convert vcell43_65_error using 1; norm_num
  · convert vcell43_66_error using 1; norm_num
  · convert vcell43_67_error using 1; norm_num
  · convert vcell43_68_error using 1; norm_num
  · convert vcell43_69_error using 1; norm_num
  · convert vcell43_70_error using 1; norm_num
  · convert vcell43_71_error using 1; norm_num
  · convert vcell43_72_error using 1; norm_num
  · convert vcell43_73_error using 1; norm_num
  · convert vcell43_74_error using 1; norm_num
  · convert vcell43_75_error using 1; norm_num
  · convert vcell43_76_error using 1; norm_num
  · convert vcell43_77_error using 1; norm_num
  · convert vcell43_78_error using 1; norm_num
  · convert vcell43_79_error using 1; norm_num
  · convert vcell43_80_error using 1; norm_num
  · convert vcell43_81_error using 1; norm_num
  · convert vcell43_82_error using 1; norm_num
  · convert vcell43_83_error using 1; norm_num
  · convert vcell43_84_error using 1; norm_num
  · convert vcell43_85_error using 1; norm_num
  · convert vcell43_86_error using 1; norm_num
  · convert vcell43_87_error using 1; norm_num
  · convert vcell43_88_error using 1; norm_num
  · convert vcell43_89_error using 1; norm_num
  · convert vcell43_90_error using 1; norm_num
  · convert vcell43_91_error using 1; norm_num
  · convert vcell43_92_error using 1; norm_num
  · convert vcell43_93_error using 1; norm_num
  · convert vcell43_94_error using 1; norm_num
  · convert vcell43_95_error using 1; norm_num
  · convert vcell43_96_error using 1; norm_num
  · convert vcell43_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
