module

public import BecknerOnofri.SpinPressureCertificateSound

@[expose] public section

/-!
# Lemma 5.20 (lem:section5-scalar-pressure) on `[1/16, 0.99]`

The interval `[1/16, 99/100] = [204800/d, 3244032/d]`, `d = 3276800`, is covered by
127 consecutive cells; on each, `checkCell` is evaluated by the kernel in its own declaration
(which keeps the memory of independent kernel checkers per declaration small). The cells
were chosen greedily by evaluating `checkCell` itself; their choice is not trusted.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

/-- The common denominator of the cell endpoints. -/
def cellDen : ℤ := 3276800

theorem cell000 : checkCell 204800 211394 cellDen = true := by decide +kernel
theorem cell001 : checkCell 211394 218235 cellDen = true := by decide +kernel
theorem cell002 : checkCell 218235 225332 cellDen = true := by decide +kernel
theorem cell003 : checkCell 225332 232694 cellDen = true := by decide +kernel
theorem cell004 : checkCell 232694 240330 cellDen = true := by decide +kernel
theorem cell005 : checkCell 240330 248249 cellDen = true := by decide +kernel
theorem cell006 : checkCell 248249 256461 cellDen = true := by decide +kernel
theorem cell007 : checkCell 256461 264975 cellDen = true := by decide +kernel
theorem cell008 : checkCell 264975 273802 cellDen = true := by decide +kernel
theorem cell009 : checkCell 273802 282951 cellDen = true := by decide +kernel
theorem cell010 : checkCell 282951 292434 cellDen = true := by decide +kernel
theorem cell011 : checkCell 292434 302261 cellDen = true := by decide +kernel
theorem cell012 : checkCell 302261 312444 cellDen = true := by decide +kernel
theorem cell013 : checkCell 312444 322994 cellDen = true := by decide +kernel
theorem cell014 : checkCell 322994 333923 cellDen = true := by decide +kernel
theorem cell015 : checkCell 333923 345243 cellDen = true := by decide +kernel
theorem cell016 : checkCell 345243 356967 cellDen = true := by decide +kernel
theorem cell017 : checkCell 356967 369107 cellDen = true := by decide +kernel
theorem cell018 : checkCell 369107 381676 cellDen = true := by decide +kernel
theorem cell019 : checkCell 381676 394687 cellDen = true := by decide +kernel
theorem cell020 : checkCell 394687 408153 cellDen = true := by decide +kernel
theorem cell021 : checkCell 408153 422089 cellDen = true := by decide +kernel
theorem cell022 : checkCell 422089 436508 cellDen = true := by decide +kernel
theorem cell023 : checkCell 436508 451425 cellDen = true := by decide +kernel
theorem cell024 : checkCell 451425 466853 cellDen = true := by decide +kernel
theorem cell025 : checkCell 466853 482807 cellDen = true := by decide +kernel
theorem cell026 : checkCell 482807 499302 cellDen = true := by decide +kernel
theorem cell027 : checkCell 499302 516353 cellDen = true := by decide +kernel
theorem cell028 : checkCell 516353 533973 cellDen = true := by decide +kernel
theorem cell029 : checkCell 533973 552178 cellDen = true := by decide +kernel
theorem cell030 : checkCell 552178 570982 cellDen = true := by decide +kernel
theorem cell031 : checkCell 570982 590399 cellDen = true := by decide +kernel
theorem cell032 : checkCell 590399 610442 cellDen = true := by decide +kernel
theorem cell033 : checkCell 610442 631125 cellDen = true := by decide +kernel
theorem cell034 : checkCell 631125 652459 cellDen = true := by decide +kernel
theorem cell035 : checkCell 652459 674455 cellDen = true := by decide +kernel
theorem cell036 : checkCell 674455 697122 cellDen = true := by decide +kernel
theorem cell037 : checkCell 697122 720470 cellDen = true := by decide +kernel
theorem cell038 : checkCell 720470 744507 cellDen = true := by decide +kernel
theorem cell039 : checkCell 744507 769239 cellDen = true := by decide +kernel
theorem cell040 : checkCell 769239 794671 cellDen = true := by decide +kernel
theorem cell041 : checkCell 794671 820807 cellDen = true := by decide +kernel
theorem cell042 : checkCell 820807 847649 cellDen = true := by decide +kernel
theorem cell043 : checkCell 847649 875197 cellDen = true := by decide +kernel
theorem cell044 : checkCell 875197 903449 cellDen = true := by decide +kernel
theorem cell045 : checkCell 903449 932402 cellDen = true := by decide +kernel
theorem cell046 : checkCell 932402 962050 cellDen = true := by decide +kernel
theorem cell047 : checkCell 962050 992388 cellDen = true := by decide +kernel
theorem cell048 : checkCell 992388 1023407 cellDen = true := by decide +kernel
theorem cell049 : checkCell 1023407 1055100 cellDen = true := by decide +kernel
theorem cell050 : checkCell 1055100 1087456 cellDen = true := by decide +kernel
theorem cell051 : checkCell 1087456 1120467 cellDen = true := by decide +kernel
theorem cell052 : checkCell 1120467 1154125 cellDen = true := by decide +kernel
theorem cell053 : checkCell 1154125 1188424 cellDen = true := by decide +kernel
theorem cell054 : checkCell 1188424 1223359 cellDen = true := by decide +kernel
theorem cell055 : checkCell 1223359 1258930 cellDen = true := by decide +kernel
theorem cell056 : checkCell 1258930 1295142 cellDen = true := by decide +kernel
theorem cell057 : checkCell 1295142 1332006 cellDen = true := by decide +kernel
theorem cell058 : checkCell 1332006 1369542 cellDen = true := by decide +kernel
theorem cell059 : checkCell 1369542 1407780 cellDen = true := by decide +kernel
theorem cell060 : checkCell 1407780 1446764 cellDen = true := by decide +kernel
theorem cell061 : checkCell 1446764 1486552 cellDen = true := by decide +kernel
theorem cell062 : checkCell 1486552 1527224 cellDen = true := by decide +kernel
theorem cell063 : checkCell 1527224 1568882 cellDen = true := by decide +kernel
theorem cell064 : checkCell 1568882 1611659 cellDen = true := by decide +kernel
theorem cell065 : checkCell 1611659 1655723 cellDen = true := by decide +kernel
theorem cell066 : checkCell 1655723 1701287 cellDen = true := by decide +kernel
theorem cell067 : checkCell 1701287 1748619 cellDen = true := by decide +kernel
theorem cell068 : checkCell 1748619 1798053 cellDen = true := by decide +kernel
theorem cell069 : checkCell 1798053 1850004 cellDen = true := by decide +kernel
theorem cell070 : checkCell 1850004 1904980 cellDen = true := by decide +kernel
theorem cell071 : checkCell 1904980 1963492 cellDen = true := by decide +kernel
theorem cell072 : checkCell 1963492 2025939 cellDen = true := by decide +kernel
theorem cell073 : checkCell 2025939 2092821 cellDen = true := by decide +kernel
theorem cell074 : checkCell 2092821 2164406 cellDen = true := by decide +kernel
theorem cell075 : checkCell 2164406 2240368 cellDen = true := by decide +kernel
theorem cell076 : checkCell 2240368 2319465 cellDen = true := by decide +kernel
theorem cell077 : checkCell 2319465 2398014 cellDen = true := by decide +kernel
theorem cell078 : checkCell 2398014 2473668 cellDen = true := by decide +kernel
theorem cell079 : checkCell 2473668 2545670 cellDen = true := by decide +kernel
theorem cell080 : checkCell 2545670 2614801 cellDen = true := by decide +kernel
theorem cell081 : checkCell 2614801 2680278 cellDen = true := by decide +kernel
theorem cell082 : checkCell 2680278 2739931 cellDen = true := by decide +kernel
theorem cell083 : checkCell 2739931 2792347 cellDen = true := by decide +kernel
theorem cell084 : checkCell 2792347 2837374 cellDen = true := by decide +kernel
theorem cell085 : checkCell 2837374 2875835 cellDen = true := by decide +kernel
theorem cell086 : checkCell 2875835 2908909 cellDen = true := by decide +kernel
theorem cell087 : checkCell 2908909 2937675 cellDen = true := by decide +kernel
theorem cell088 : checkCell 2937675 2962950 cellDen = true := by decide +kernel
theorem cell089 : checkCell 2962950 2985399 cellDen = true := by decide +kernel
theorem cell090 : checkCell 2985399 3005527 cellDen = true := by decide +kernel
theorem cell091 : checkCell 3005527 3023713 cellDen = true := by decide +kernel
theorem cell092 : checkCell 3023713 3040248 cellDen = true := by decide +kernel
theorem cell093 : checkCell 3040248 3055361 cellDen = true := by decide +kernel
theorem cell094 : checkCell 3055361 3069233 cellDen = true := by decide +kernel
theorem cell095 : checkCell 3069233 3082011 cellDen = true := by decide +kernel
theorem cell096 : checkCell 3082011 3093818 cellDen = true := by decide +kernel
theorem cell097 : checkCell 3093818 3104755 cellDen = true := by decide +kernel
theorem cell098 : checkCell 3104755 3114910 cellDen = true := by decide +kernel
theorem cell099 : checkCell 3114910 3124357 cellDen = true := by decide +kernel
theorem cell100 : checkCell 3124357 3133161 cellDen = true := by decide +kernel
theorem cell101 : checkCell 3133161 3141380 cellDen = true := by decide +kernel
theorem cell102 : checkCell 3141380 3149064 cellDen = true := by decide +kernel
theorem cell103 : checkCell 3149064 3156259 cellDen = true := by decide +kernel
theorem cell104 : checkCell 3156259 3163004 cellDen = true := by decide +kernel
theorem cell105 : checkCell 3163004 3169336 cellDen = true := by decide +kernel
theorem cell106 : checkCell 3169336 3175287 cellDen = true := by decide +kernel
theorem cell107 : checkCell 3175287 3180887 cellDen = true := by decide +kernel
theorem cell108 : checkCell 3180887 3186162 cellDen = true := by decide +kernel
theorem cell109 : checkCell 3186162 3191136 cellDen = true := by decide +kernel
theorem cell110 : checkCell 3191136 3195832 cellDen = true := by decide +kernel
theorem cell111 : checkCell 3195832 3200269 cellDen = true := by decide +kernel
theorem cell112 : checkCell 3200269 3204466 cellDen = true := by decide +kernel
theorem cell113 : checkCell 3204466 3208440 cellDen = true := by decide +kernel
theorem cell114 : checkCell 3208440 3212206 cellDen = true := by decide +kernel
theorem cell115 : checkCell 3212206 3215777 cellDen = true := by decide +kernel
theorem cell116 : checkCell 3215777 3219167 cellDen = true := by decide +kernel
theorem cell117 : checkCell 3219167 3222387 cellDen = true := by decide +kernel
theorem cell118 : checkCell 3222387 3225447 cellDen = true := by decide +kernel
theorem cell119 : checkCell 3225447 3228358 cellDen = true := by decide +kernel
theorem cell120 : checkCell 3228358 3231128 cellDen = true := by decide +kernel
theorem cell121 : checkCell 3231128 3233765 cellDen = true := by decide +kernel
theorem cell122 : checkCell 3233765 3236276 cellDen = true := by decide +kernel
theorem cell123 : checkCell 3236276 3238667 cellDen = true := by decide +kernel
theorem cell124 : checkCell 3238667 3240944 cellDen = true := by decide +kernel
theorem cell125 : checkCell 3240944 3243111 cellDen = true := by decide +kernel
theorem cell126 : checkCell 3243111 3244032 cellDen = true := by decide +kernel

/-- All cells, in order. -/
def cells : List (ℤ × ℤ) :=
  [(204800, 211394), (211394, 218235), (218235, 225332), (225332, 232694), (232694, 240330),
   (240330, 248249), (248249, 256461), (256461, 264975), (264975, 273802), (273802, 282951),
   (282951, 292434), (292434, 302261), (302261, 312444), (312444, 322994), (322994, 333923),
   (333923, 345243), (345243, 356967), (356967, 369107), (369107, 381676), (381676, 394687),
   (394687, 408153), (408153, 422089), (422089, 436508), (436508, 451425), (451425, 466853),
   (466853, 482807), (482807, 499302), (499302, 516353), (516353, 533973), (533973, 552178),
   (552178, 570982), (570982, 590399), (590399, 610442), (610442, 631125), (631125, 652459),
   (652459, 674455), (674455, 697122), (697122, 720470), (720470, 744507), (744507, 769239),
   (769239, 794671), (794671, 820807), (820807, 847649), (847649, 875197), (875197, 903449),
   (903449, 932402), (932402, 962050), (962050, 992388), (992388, 1023407), (1023407, 1055100),
   (1055100, 1087456), (1087456, 1120467), (1120467, 1154125), (1154125, 1188424),
   (1188424, 1223359), (1223359, 1258930), (1258930, 1295142), (1295142, 1332006),
   (1332006, 1369542), (1369542, 1407780), (1407780, 1446764), (1446764, 1486552),
   (1486552, 1527224), (1527224, 1568882), (1568882, 1611659), (1611659, 1655723),
   (1655723, 1701287), (1701287, 1748619), (1748619, 1798053), (1798053, 1850004),
   (1850004, 1904980), (1904980, 1963492), (1963492, 2025939), (2025939, 2092821),
   (2092821, 2164406), (2164406, 2240368), (2240368, 2319465), (2319465, 2398014),
   (2398014, 2473668), (2473668, 2545670), (2545670, 2614801), (2614801, 2680278),
   (2680278, 2739931), (2739931, 2792347), (2792347, 2837374), (2837374, 2875835),
   (2875835, 2908909), (2908909, 2937675), (2937675, 2962950), (2962950, 2985399),
   (2985399, 3005527), (3005527, 3023713), (3023713, 3040248), (3040248, 3055361),
   (3055361, 3069233), (3069233, 3082011), (3082011, 3093818), (3093818, 3104755),
   (3104755, 3114910), (3114910, 3124357), (3124357, 3133161), (3133161, 3141380),
   (3141380, 3149064), (3149064, 3156259), (3156259, 3163004), (3163004, 3169336),
   (3169336, 3175287), (3175287, 3180887), (3180887, 3186162), (3186162, 3191136),
   (3191136, 3195832), (3195832, 3200269), (3200269, 3204466), (3204466, 3208440),
   (3208440, 3212206), (3212206, 3215777), (3215777, 3219167), (3219167, 3222387),
   (3222387, 3225447), (3225447, 3228358), (3228358, 3231128), (3231128, 3233765),
   (3233765, 3236276), (3236276, 3238667), (3238667, 3240944), (3240944, 3243111),
   (3243111, 3244032)]

/-- Every cell passes. -/
theorem cells_check : ∀ c ∈ cells, checkCell c.1 c.2 cellDen = true := by
  simp only [cells, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨cell000, cell001, cell002, cell003, cell004, cell005, cell006, cell007, cell008, cell009,
    cell010, cell011, cell012, cell013, cell014, cell015, cell016, cell017, cell018, cell019,
    cell020, cell021, cell022, cell023, cell024, cell025, cell026, cell027, cell028, cell029,
    cell030, cell031, cell032, cell033, cell034, cell035, cell036, cell037, cell038, cell039,
    cell040, cell041, cell042, cell043, cell044, cell045, cell046, cell047, cell048, cell049,
    cell050, cell051, cell052, cell053, cell054, cell055, cell056, cell057, cell058, cell059,
    cell060, cell061, cell062, cell063, cell064, cell065, cell066, cell067, cell068, cell069,
    cell070, cell071, cell072, cell073, cell074, cell075, cell076, cell077, cell078, cell079,
    cell080, cell081, cell082, cell083, cell084, cell085, cell086, cell087, cell088, cell089,
    cell090, cell091, cell092, cell093, cell094, cell095, cell096, cell097, cell098, cell099,
    cell100, cell101, cell102, cell103, cell104, cell105, cell106, cell107, cell108, cell109,
    cell110, cell111, cell112, cell113, cell114, cell115, cell116, cell117, cell118, cell119,
    cell120, cell121, cell122, cell123, cell124, cell125, cell126⟩

end BecknerOnofri.HighDim.Spin.PressureCertificate
