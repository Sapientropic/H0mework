import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_033_047
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_047_059
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_059_068
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_068_081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_081_094
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033_094_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_33 (j : Basis) (ordered : (33 : Basis) ≤ j) :
    |aoIntegral (33 : Basis) j - (recordedAttraction (33 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (33 : Basis) = ⟨33,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(33 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (30 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (31 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(33 : Basis) ≤ (32 : Basis) by decide) ordered)
  · convert vcell33_33_error using 1; norm_num
  · convert vcell33_34_error using 1; norm_num
  · convert vcell33_35_error using 1; norm_num
  · convert vcell33_36_error using 1; norm_num
  · convert vcell33_37_error using 1; norm_num
  · convert vcell33_38_error using 1; norm_num
  · convert vcell33_39_error using 1; norm_num
  · convert vcell33_40_error using 1; norm_num
  · convert vcell33_41_error using 1; norm_num
  · convert vcell33_42_error using 1; norm_num
  · convert vcell33_43_error using 1; norm_num
  · convert vcell33_44_error using 1; norm_num
  · convert vcell33_45_error using 1; norm_num
  · convert vcell33_46_error using 1; norm_num
  · convert vcell33_47_error using 1; norm_num
  · convert vcell33_48_error using 1; norm_num
  · convert vcell33_49_error using 1; norm_num
  · convert vcell33_50_error using 1; norm_num
  · convert vcell33_51_error using 1; norm_num
  · convert vcell33_52_error using 1; norm_num
  · convert vcell33_53_error using 1; norm_num
  · convert vcell33_54_error using 1; norm_num
  · convert vcell33_55_error using 1; norm_num
  · convert vcell33_56_error using 1; norm_num
  · convert vcell33_57_error using 1; norm_num
  · convert vcell33_58_error using 1; norm_num
  · convert vcell33_59_error using 1; norm_num
  · convert vcell33_60_error using 1; norm_num
  · convert vcell33_61_error using 1; norm_num
  · convert vcell33_62_error using 1; norm_num
  · convert vcell33_63_error using 1; norm_num
  · convert vcell33_64_error using 1; norm_num
  · convert vcell33_65_error using 1; norm_num
  · convert vcell33_66_error using 1; norm_num
  · convert vcell33_67_error using 1; norm_num
  · convert vcell33_68_error using 1; norm_num
  · convert vcell33_69_error using 1; norm_num
  · convert vcell33_70_error using 1; norm_num
  · convert vcell33_71_error using 1; norm_num
  · convert vcell33_72_error using 1; norm_num
  · convert vcell33_73_error using 1; norm_num
  · convert vcell33_74_error using 1; norm_num
  · convert vcell33_75_error using 1; norm_num
  · convert vcell33_76_error using 1; norm_num
  · convert vcell33_77_error using 1; norm_num
  · convert vcell33_78_error using 1; norm_num
  · convert vcell33_79_error using 1; norm_num
  · convert vcell33_80_error using 1; norm_num
  · convert vcell33_81_error using 1; norm_num
  · convert vcell33_82_error using 1; norm_num
  · convert vcell33_83_error using 1; norm_num
  · convert vcell33_84_error using 1; norm_num
  · convert vcell33_85_error using 1; norm_num
  · convert vcell33_86_error using 1; norm_num
  · convert vcell33_87_error using 1; norm_num
  · convert vcell33_88_error using 1; norm_num
  · convert vcell33_89_error using 1; norm_num
  · convert vcell33_90_error using 1; norm_num
  · convert vcell33_91_error using 1; norm_num
  · convert vcell33_92_error using 1; norm_num
  · convert vcell33_93_error using 1; norm_num
  · convert vcell33_94_error using 1; norm_num
  · convert vcell33_95_error using 1; norm_num
  · convert vcell33_96_error using 1; norm_num
  · convert vcell33_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
