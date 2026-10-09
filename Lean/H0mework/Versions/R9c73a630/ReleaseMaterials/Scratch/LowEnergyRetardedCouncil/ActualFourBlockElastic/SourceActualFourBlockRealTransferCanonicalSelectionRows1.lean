import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalSelection
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

def canonicalInverseSelectorRow40 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (185,2)
  | 5 => some (193,2)
  | 14 => some (212,2)
  | 15 => some (201,2)
  | 26 => some (201,2)
  | 27 => some (200,2)
  | 40 => some (215,2)
  | 41 => some (221,2)
  | 59 => some (223,2)
  | 65 => some (222,2)
  | 69 => some (220,2)
  | 75 => some (219,2)
  | _ => none

theorem actual_canonical_inverse_row40 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 40 b = scaling 40 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow40 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow41 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (186,2)
  | 5 => some (185,2)
  | 14 => some (208,2)
  | 15 => some (212,2)
  | 26 => some (212,2)
  | 27 => some (201,2)
  | 40 => some (216,2)
  | 41 => some (215,2)
  | 59 => some (220,2)
  | 65 => some (219,2)
  | 69 => some (218,2)
  | 75 => some (217,2)
  | _ => none

theorem actual_canonical_inverse_row41 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 41 b = scaling 41 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow41 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow42 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (241,3)
  | 7 => some (265,3)
  | 10 => some (286,3)
  | 11 => some (298,3)
  | 12 => some (373,3)
  | 13 => some (333,3)
  | 24 => some (348,3)
  | 25 => some (374,3)
  | 42 => some (375,3)
  | 43 => some (376,3)
  | 46 => some (377,3)
  | 47 => some (378,3)
  | 48 => some (379,3)
  | 50 => some (380,3)
  | 52 => some (381,3)
  | 53 => some (382,3)
  | 54 => some (383,3)
  | 57 => some (384,3)
  | 58 => some (385,3)
  | 60 => some (386,3)
  | 64 => some (387,3)
  | 66 => some (388,3)
  | 70 => some (389,3)
  | 74 => some (390,3)
  | 76 => some (391,3)
  | _ => none

theorem actual_canonical_inverse_row42 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 42 b = scaling 42 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow42 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow43 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (242,3)
  | 7 => some (266,3)
  | 10 => some (287,3)
  | 11 => some (299,3)
  | 12 => some (392,3)
  | 13 => some (334,3)
  | 24 => some (349,3)
  | 25 => some (393,3)
  | 42 => some (376,3)
  | 43 => some (394,3)
  | 46 => some (395,3)
  | 47 => some (396,3)
  | 48 => some (397,3)
  | 50 => some (398,3)
  | 52 => some (399,3)
  | 53 => some (400,3)
  | 54 => some (401,3)
  | 57 => some (402,3)
  | 58 => some (403,3)
  | 60 => some (404,3)
  | 64 => some (405,3)
  | 66 => some (406,3)
  | 70 => some (407,3)
  | 74 => some (408,3)
  | 76 => some (409,3)
  | _ => none

theorem actual_canonical_inverse_row43 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 43 b = scaling 43 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow43 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow44 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 8 => some (523,4)
  | 44 => some (524,4)
  | _ => none

theorem actual_canonical_inverse_row44 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 44 b = scaling 44 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow44 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow45 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 9 => some (523,5)
  | 45 => some (524,5)
  | _ => none

theorem actual_canonical_inverse_row45 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 45 b = scaling 45 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow45 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow46 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (243,3)
  | 7 => some (267,3)
  | 10 => some (288,3)
  | 11 => some (289,3)
  | 12 => some (358,3)
  | 25 => some (314,3)
  | 42 => some (377,3)
  | 43 => some (395,3)
  | 46 => some (410,3)
  | 47 => some (411,3)
  | 58 => some (412,3)
  | 60 => some (413,3)
  | 64 => some (413,3)
  | 66 => some (412,3)
  | 70 => some (414,3)
  | 74 => some (415,3)
  | 76 => some (416,3)
  | _ => none

theorem actual_canonical_inverse_row46 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 46 b = scaling 46 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow46 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow47 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (244,3)
  | 7 => some (268,3)
  | 10 => some (289,3)
  | 11 => some (300,3)
  | 12 => some (359,3)
  | 25 => some (315,3)
  | 42 => some (378,3)
  | 43 => some (396,3)
  | 46 => some (411,3)
  | 47 => some (417,3)
  | 58 => some (418,3)
  | 60 => some (419,3)
  | 64 => some (419,3)
  | 66 => some (418,3)
  | 70 => some (420,3)
  | 74 => some (421,3)
  | 76 => some (422,3)
  | _ => none

theorem actual_canonical_inverse_row47 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 47 b = scaling 47 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow47 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow48 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (245,3)
  | 7 => some (269,3)
  | 12 => some (360,3)
  | 13 => some (335,3)
  | 24 => some (335,3)
  | 25 => some (316,3)
  | 42 => some (379,3)
  | 43 => some (397,3)
  | 48 => some (423,3)
  | 50 => some (424,3)
  | 53 => some (424,3)
  | 54 => some (425,3)
  | 57 => some (426,3)
  | 58 => some (427,3)
  | 60 => some (428,3)
  | 64 => some (429,3)
  | 66 => some (430,3)
  | 70 => some (431,3)
  | 74 => some (431,3)
  | _ => none

theorem actual_canonical_inverse_row48 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 48 b = scaling 48 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow48 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow49 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (28,0)
  | 1 => some (13,0)
  | 18 => some (43,0)
  | 19 => some (61,0)
  | 30 => some (44,0)
  | 31 => some (62,0)
  | 36 => some (132,0)
  | 37 => some (122,0)
  | 49 => some (137,0)
  | 51 => some (138,0)
  | 55 => some (139,0)
  | 56 => some (140,0)
  | 61 => some (141,0)
  | 63 => some (141,0)
  | 71 => some (142,0)
  | 73 => some (143,0)
  | _ => none

theorem actual_canonical_inverse_row49 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 49 b = scaling 49 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow49 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow50 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (246,3)
  | 7 => some (270,3)
  | 12 => some (432,3)
  | 13 => some (336,3)
  | 24 => some (338,3)
  | 25 => some (433,3)
  | 42 => some (380,3)
  | 43 => some (398,3)
  | 48 => some (424,3)
  | 50 => some (434,3)
  | 52 => some (435,3)
  | 53 => some (436,3)
  | 54 => some (437,3)
  | 57 => some (438,3)
  | 58 => some (439,3)
  | 60 => some (440,3)
  | 64 => some (441,3)
  | 66 => some (442,3)
  | 70 => some (443,3)
  | 74 => some (443,3)
  | _ => none

theorem actual_canonical_inverse_row50 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 50 b = scaling 50 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow50 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow51 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (13,0)
  | 1 => some (12,0)
  | 18 => some (62,0)
  | 19 => some (44,0)
  | 30 => some (43,0)
  | 31 => some (61,0)
  | 36 => some (122,0)
  | 37 => some (121,0)
  | 49 => some (144,0)
  | 51 => some (137,0)
  | 55 => some (145,0)
  | 56 => some (139,0)
  | 61 => some (143,0)
  | 63 => some (143,0)
  | 71 => some (141,0)
  | 73 => some (146,0)
  | _ => none

theorem actual_canonical_inverse_row51 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 51 b = scaling 51 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow51 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow52 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (271,3)
  | 7 => some (247,3)
  | 12 => some (318,3)
  | 13 => some (350,3)
  | 24 => some (337,3)
  | 25 => some (362,3)
  | 42 => some (399,3)
  | 43 => some (381,3)
  | 50 => some (444,3)
  | 52 => some (445,3)
  | 53 => some (435,3)
  | _ => none

theorem actual_canonical_inverse_row52 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 52 b = scaling 52 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow52 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow53 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (248,3)
  | 7 => some (272,3)
  | 12 => some (446,3)
  | 13 => some (338,3)
  | 24 => some (336,3)
  | 25 => some (447,3)
  | 42 => some (382,3)
  | 43 => some (400,3)
  | 48 => some (424,3)
  | 50 => some (436,3)
  | 52 => some (444,3)
  | 53 => some (434,3)
  | 54 => some (437,3)
  | 57 => some (438,3)
  | 58 => some (439,3)
  | 60 => some (440,3)
  | 64 => some (441,3)
  | 66 => some (442,3)
  | 70 => some (443,3)
  | 74 => some (443,3)
  | _ => none

theorem actual_canonical_inverse_row53 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 53 b = scaling 53 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow53 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow54 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (249,3)
  | 7 => some (273,3)
  | 12 => some (364,3)
  | 13 => some (339,3)
  | 24 => some (339,3)
  | 25 => some (320,3)
  | 42 => some (383,3)
  | 43 => some (401,3)
  | 48 => some (425,3)
  | 50 => some (437,3)
  | 53 => some (437,3)
  | 54 => some (448,3)
  | 57 => some (449,3)
  | 58 => some (450,3)
  | 60 => some (451,3)
  | 64 => some (452,3)
  | 66 => some (453,3)
  | 70 => some (454,3)
  | 74 => some (454,3)
  | _ => none

theorem actual_canonical_inverse_row54 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 54 b = scaling 54 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow54 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow55 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (29,0)
  | 1 => some (15,0)
  | 18 => some (45,0)
  | 19 => some (63,0)
  | 30 => some (46,0)
  | 31 => some (64,0)
  | 36 => some (133,0)
  | 37 => some (124,0)
  | 49 => some (139,0)
  | 51 => some (140,0)
  | 55 => some (147,0)
  | 56 => some (148,0)
  | 61 => some (149,0)
  | 63 => some (149,0)
  | 71 => some (150,0)
  | 73 => some (151,0)
  | _ => none

theorem actual_canonical_inverse_row55 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 55 b = scaling 55 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow55 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow56 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (15,0)
  | 1 => some (14,0)
  | 18 => some (64,0)
  | 19 => some (46,0)
  | 30 => some (45,0)
  | 31 => some (63,0)
  | 36 => some (124,0)
  | 37 => some (123,0)
  | 49 => some (145,0)
  | 51 => some (139,0)
  | 55 => some (152,0)
  | 56 => some (147,0)
  | 61 => some (151,0)
  | 63 => some (151,0)
  | 71 => some (149,0)
  | 73 => some (153,0)
  | _ => none

theorem actual_canonical_inverse_row56 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 56 b = scaling 56 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow56 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow57 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (250,3)
  | 7 => some (274,3)
  | 12 => some (365,3)
  | 13 => some (340,3)
  | 24 => some (340,3)
  | 25 => some (321,3)
  | 42 => some (384,3)
  | 43 => some (402,3)
  | 48 => some (426,3)
  | 50 => some (438,3)
  | 53 => some (438,3)
  | 54 => some (449,3)
  | 57 => some (455,3)
  | 58 => some (456,3)
  | 60 => some (457,3)
  | 64 => some (458,3)
  | 66 => some (459,3)
  | 70 => some (460,3)
  | 74 => some (460,3)
  | _ => none

theorem actual_canonical_inverse_row57 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 57 b = scaling 57 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow57 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow58 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (251,3)
  | 7 => some (275,3)
  | 10 => some (290,3)
  | 11 => some (301,3)
  | 12 => some (366,3)
  | 13 => some (341,3)
  | 24 => some (341,3)
  | 25 => some (322,3)
  | 42 => some (385,3)
  | 43 => some (403,3)
  | 46 => some (412,3)
  | 47 => some (418,3)
  | 48 => some (427,3)
  | 50 => some (439,3)
  | 53 => some (439,3)
  | 54 => some (450,3)
  | 57 => some (456,3)
  | 58 => some (461,3)
  | 60 => some (462,3)
  | 64 => some (463,3)
  | 66 => some (464,3)
  | 70 => some (465,3)
  | 74 => some (466,3)
  | 76 => some (467,3)
  | _ => none

theorem actual_canonical_inverse_row58 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 58 b = scaling 58 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow58 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow59 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (188,2)
  | 5 => some (190,2)
  | 14 => some (210,2)
  | 15 => some (214,2)
  | 26 => some (214,2)
  | 27 => some (203,2)
  | 40 => some (218,2)
  | 41 => some (220,2)
  | 59 => some (228,2)
  | 65 => some (225,2)
  | 69 => some (232,2)
  | 75 => some (231,2)
  | _ => none

theorem actual_canonical_inverse_row59 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 59 b = scaling 59 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow59 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow60 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (252,3)
  | 7 => some (276,3)
  | 10 => some (291,3)
  | 11 => some (302,3)
  | 12 => some (367,3)
  | 13 => some (342,3)
  | 24 => some (342,3)
  | 25 => some (323,3)
  | 42 => some (386,3)
  | 43 => some (404,3)
  | 46 => some (413,3)
  | 47 => some (419,3)
  | 48 => some (428,3)
  | 50 => some (440,3)
  | 53 => some (440,3)
  | 54 => some (451,3)
  | 57 => some (457,3)
  | 58 => some (462,3)
  | 60 => some (468,3)
  | 64 => some (469,3)
  | 66 => some (463,3)
  | 70 => some (470,3)
  | 74 => some (471,3)
  | 76 => some (472,3)
  | _ => none

theorem actual_canonical_inverse_row60 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 60 b = scaling 60 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow60 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow61 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (31,0)
  | 1 => some (19,0)
  | 18 => some (47,0)
  | 19 => some (65,0)
  | 22 => some (77,0)
  | 23 => some (87,0)
  | 30 => some (50,0)
  | 31 => some (68,0)
  | 34 => some (80,0)
  | 35 => some (90,0)
  | 36 => some (135,0)
  | 37 => some (128,0)
  | 49 => some (141,0)
  | 51 => some (142,0)
  | 55 => some (149,0)
  | 56 => some (150,0)
  | 61 => some (154,0)
  | 63 => some (155,0)
  | 67 => some (156,0)
  | 71 => some (157,0)
  | 73 => some (158,0)
  | 77 => some (159,0)
  | _ => none

theorem actual_canonical_inverse_row61 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 61 b = scaling 61 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow61 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow62 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (194,1)
  | 3 => some (189,1)
  | 16 => some (209,1)
  | 17 => some (204,1)
  | 28 => some (213,1)
  | 29 => some (209,1)
  | 38 => some (222,1)
  | 39 => some (219,1)
  | 62 => some (224,1)
  | 68 => some (225,1)
  | 72 => some (226,1)
  | 78 => some (227,1)
  | _ => none

theorem actual_canonical_inverse_row62 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 62 b = scaling 62 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow62 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow63 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (160,0)
  | 1 => some (30,0)
  | 18 => some (48,0)
  | 19 => some (66,0)
  | 22 => some (78,0)
  | 23 => some (88,0)
  | 30 => some (161,0)
  | 31 => some (162,0)
  | 34 => some (163,0)
  | 35 => some (164,0)
  | 36 => some (165,0)
  | 37 => some (134,0)
  | 49 => some (141,0)
  | 51 => some (142,0)
  | 55 => some (149,0)
  | 56 => some (150,0)
  | 61 => some (155,0)
  | 63 => some (166,0)
  | 67 => some (167,0)
  | 71 => some (168,0)
  | 73 => some (169,0)
  | 77 => some (170,0)
  | _ => none

theorem actual_canonical_inverse_row63 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 63 b = scaling 63 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow63 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow64 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (253,3)
  | 7 => some (277,3)
  | 10 => some (291,3)
  | 11 => some (302,3)
  | 12 => some (368,3)
  | 13 => some (343,3)
  | 24 => some (343,3)
  | 25 => some (324,3)
  | 42 => some (387,3)
  | 43 => some (405,3)
  | 46 => some (413,3)
  | 47 => some (419,3)
  | 48 => some (429,3)
  | 50 => some (441,3)
  | 53 => some (441,3)
  | 54 => some (452,3)
  | 57 => some (458,3)
  | 58 => some (463,3)
  | 60 => some (469,3)
  | 64 => some (468,3)
  | 66 => some (462,3)
  | 70 => some (473,3)
  | 74 => some (474,3)
  | 76 => some (472,3)
  | _ => none

theorem actual_canonical_inverse_row64 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 64 b = scaling 64 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow64 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow65 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (187,2)
  | 5 => some (189,2)
  | 14 => some (209,2)
  | 15 => some (213,2)
  | 26 => some (213,2)
  | 27 => some (202,2)
  | 40 => some (217,2)
  | 41 => some (219,2)
  | 59 => some (225,2)
  | 65 => some (224,2)
  | 69 => some (231,2)
  | 75 => some (230,2)
  | _ => none

theorem actual_canonical_inverse_row65 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 65 b = scaling 65 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow65 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow66 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (254,3)
  | 7 => some (278,3)
  | 10 => some (290,3)
  | 11 => some (301,3)
  | 12 => some (369,3)
  | 13 => some (344,3)
  | 24 => some (344,3)
  | 25 => some (325,3)
  | 42 => some (388,3)
  | 43 => some (406,3)
  | 46 => some (412,3)
  | 47 => some (418,3)
  | 48 => some (430,3)
  | 50 => some (442,3)
  | 53 => some (442,3)
  | 54 => some (453,3)
  | 57 => some (459,3)
  | 58 => some (464,3)
  | 60 => some (463,3)
  | 64 => some (462,3)
  | 66 => some (461,3)
  | 70 => some (475,3)
  | 74 => some (476,3)
  | 76 => some (467,3)
  | _ => none

theorem actual_canonical_inverse_row66 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 66 b = scaling 66 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow66 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow67 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (32,0)
  | 1 => some (21,0)
  | 18 => some (49,0)
  | 19 => some (67,0)
  | 22 => some (79,0)
  | 23 => some (89,0)
  | 30 => some (52,0)
  | 31 => some (70,0)
  | 34 => some (82,0)
  | 35 => some (92,0)
  | 36 => some (136,0)
  | 37 => some (130,0)
  | 61 => some (156,0)
  | 63 => some (167,0)
  | 67 => some (171,0)
  | 71 => some (159,0)
  | 73 => some (172,0)
  | 77 => some (173,0)
  | _ => none

theorem actual_canonical_inverse_row67 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 67 b = scaling 67 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow67 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow68 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (195,1)
  | 3 => some (190,1)
  | 16 => some (210,1)
  | 17 => some (205,1)
  | 28 => some (214,1)
  | 29 => some (210,1)
  | 38 => some (223,1)
  | 39 => some (220,1)
  | 62 => some (225,1)
  | 68 => some (228,1)
  | 72 => some (227,1)
  | 78 => some (229,1)
  | _ => none

theorem actual_canonical_inverse_row68 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 68 b = scaling 68 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow68 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow69 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (190,2)
  | 5 => some (195,2)
  | 14 => some (214,2)
  | 15 => some (203,2)
  | 26 => some (203,2)
  | 27 => some (205,2)
  | 40 => some (220,2)
  | 41 => some (223,2)
  | 59 => some (229,2)
  | 65 => some (227,2)
  | 69 => some (228,2)
  | 75 => some (225,2)
  | _ => none

theorem actual_canonical_inverse_row69 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 69 b = scaling 69 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow69 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow70 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (477,3)
  | 7 => some (478,3)
  | 10 => some (479,3)
  | 11 => some (480,3)
  | 12 => some (326,3)
  | 13 => some (481,3)
  | 24 => some (481,3)
  | 25 => some (370,3)
  | 42 => some (482,3)
  | 43 => some (483,3)
  | 46 => some (484,3)
  | 47 => some (485,3)
  | 48 => some (486,3)
  | 50 => some (487,3)
  | 53 => some (487,3)
  | 54 => some (488,3)
  | 57 => some (489,3)
  | 58 => some (490,3)
  | 60 => some (491,3)
  | 64 => some (492,3)
  | 66 => some (493,3)
  | 70 => some (494,3)
  | 74 => some (495,3)
  | 76 => some (496,3)
  | _ => none

theorem actual_canonical_inverse_row70 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 70 b = scaling 70 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow70 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow71 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (19,0)
  | 1 => some (16,0)
  | 18 => some (98,0)
  | 19 => some (105,0)
  | 22 => some (111,0)
  | 23 => some (116,0)
  | 30 => some (47,0)
  | 31 => some (65,0)
  | 34 => some (77,0)
  | 35 => some (87,0)
  | 36 => some (128,0)
  | 37 => some (125,0)
  | 49 => some (143,0)
  | 51 => some (141,0)
  | 55 => some (151,0)
  | 56 => some (149,0)
  | 61 => some (174,0)
  | 63 => some (158,0)
  | 67 => some (175,0)
  | 71 => some (154,0)
  | 73 => some (176,0)
  | 77 => some (156,0)
  | _ => none

theorem actual_canonical_inverse_row71 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 71 b = scaling 71 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow71 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow72 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (189,1)
  | 3 => some (187,1)
  | 16 => some (204,1)
  | 17 => some (202,1)
  | 28 => some (209,1)
  | 29 => some (204,1)
  | 38 => some (219,1)
  | 39 => some (217,1)
  | 62 => some (230,1)
  | 68 => some (231,1)
  | 72 => some (224,1)
  | 78 => some (225,1)
  | _ => none

theorem actual_canonical_inverse_row72 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 72 b = scaling 72 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow72 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow73 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (20,0)
  | 1 => some (160,0)
  | 18 => some (161,0)
  | 19 => some (162,0)
  | 22 => some (163,0)
  | 23 => some (164,0)
  | 30 => some (100,0)
  | 31 => some (107,0)
  | 34 => some (113,0)
  | 35 => some (118,0)
  | 36 => some (129,0)
  | 37 => some (165,0)
  | 49 => some (142,0)
  | 51 => some (146,0)
  | 55 => some (150,0)
  | 56 => some (153,0)
  | 61 => some (168,0)
  | 63 => some (177,0)
  | 67 => some (170,0)
  | 71 => some (176,0)
  | 73 => some (166,0)
  | 77 => some (178,0)
  | _ => none

theorem actual_canonical_inverse_row73 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 73 b = scaling 73 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow73 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow74 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (497,3)
  | 7 => some (498,3)
  | 10 => some (499,3)
  | 11 => some (500,3)
  | 12 => some (327,3)
  | 13 => some (481,3)
  | 24 => some (481,3)
  | 25 => some (371,3)
  | 42 => some (501,3)
  | 43 => some (502,3)
  | 46 => some (503,3)
  | 47 => some (504,3)
  | 48 => some (486,3)
  | 50 => some (487,3)
  | 53 => some (487,3)
  | 54 => some (488,3)
  | 57 => some (489,3)
  | 58 => some (505,3)
  | 60 => some (506,3)
  | 64 => some (507,3)
  | 66 => some (508,3)
  | 70 => some (495,3)
  | 74 => some (509,3)
  | 76 => some (510,3)
  | _ => none

theorem actual_canonical_inverse_row74 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 74 b = scaling 74 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow74 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow75 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (189,2)
  | 5 => some (194,2)
  | 14 => some (213,2)
  | 15 => some (202,2)
  | 26 => some (202,2)
  | 27 => some (204,2)
  | 40 => some (219,2)
  | 41 => some (222,2)
  | 59 => some (227,2)
  | 65 => some (226,2)
  | 69 => some (225,2)
  | 75 => some (224,2)
  | _ => none

theorem actual_canonical_inverse_row75 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 75 b = scaling 75 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow75 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow76 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (511,3)
  | 7 => some (512,3)
  | 10 => some (513,3)
  | 11 => some (514,3)
  | 12 => some (328,3)
  | 25 => some (372,3)
  | 42 => some (515,3)
  | 43 => some (516,3)
  | 46 => some (517,3)
  | 47 => some (518,3)
  | 58 => some (519,3)
  | 60 => some (520,3)
  | 64 => some (520,3)
  | 66 => some (519,3)
  | 70 => some (496,3)
  | 74 => some (510,3)
  | 76 => some (521,3)
  | _ => none

theorem actual_canonical_inverse_row76 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 76 b = scaling 76 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow76 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow77 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (21,0)
  | 1 => some (18,0)
  | 18 => some (99,0)
  | 19 => some (106,0)
  | 22 => some (112,0)
  | 23 => some (117,0)
  | 30 => some (49,0)
  | 31 => some (67,0)
  | 34 => some (79,0)
  | 35 => some (89,0)
  | 36 => some (130,0)
  | 37 => some (127,0)
  | 61 => some (175,0)
  | 63 => some (172,0)
  | 67 => some (179,0)
  | 71 => some (156,0)
  | 73 => some (178,0)
  | 77 => some (171,0)
  | _ => none

theorem actual_canonical_inverse_row77 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 77 b = scaling 77 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow77 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow78 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (190,1)
  | 3 => some (188,1)
  | 16 => some (205,1)
  | 17 => some (203,1)
  | 28 => some (210,1)
  | 29 => some (205,1)
  | 38 => some (220,1)
  | 39 => some (218,1)
  | 62 => some (231,1)
  | 68 => some (232,1)
  | 72 => some (225,1)
  | 78 => some (228,1)
  | _ => none

theorem actual_canonical_inverse_row78 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 78 b = scaling 78 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow78 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

end LowEnergy.ActualFourBlockRealTransfer
