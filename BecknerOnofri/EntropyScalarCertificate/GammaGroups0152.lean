module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0190
public import BecknerOnofri.EntropyScalarCertificate.Bessel0191
public import BecknerOnofri.EntropyScalarCertificate.Bessel0583
public import BecknerOnofri.EntropyScalarCertificate.Bessel0584
public import BecknerOnofri.EntropyScalarCertificate.Brackets0076
public import BecknerOnofri.EntropyScalarCertificate.Logs0152
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1216
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (10006864772189714833749767006407043078787/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10006864772189714833749767006407043078787/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (5018711841488698636759305988416008277117/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5018711841488698636759305988416008277117/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (20044288455167112107268378983239059633021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20044288455167112107268378983239059633021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1216 BracketBatch0076.bracket1217 (20044288455167112107268378983239059633021/20000000000000000000000000000000000000000) (3023294532040345653440898416005595513/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1216 BracketBatch0076.bracket1217
  (20044288455167112107268378983239059633021/20000000000000000000000000000000000000000) (3023294532040345653440898416005595513/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1216
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1217
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (10037423682977397273518611976832016554231/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10037423682977397273518611976832016554231/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (2013627806888539225302856438295539343517/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2013627806888539225302856438295539343517/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (2513195339677511675004111771038714158977/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2513195339677511675004111771038714158977/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1217 BracketBatch0076.bracket1218 (2513195339677511675004111771038714158977/2500000000000000000000000000000000000000) (121767947275250677172114724292898851297/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1217 BracketBatch0076.bracket1218
  (2513195339677511675004111771038714158977/2500000000000000000000000000000000000000) (121767947275250677172114724292898851297/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1217
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1218
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (5034069517221348063257141095738848358791/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5034069517221348063257141095738848358791/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2524753109835880344014442689355569125517/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2524753109835880344014442689355569125517/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (403343029475724350051441058977999464393/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (403343029475724350051441058977999464393/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1218 BracketBatch0076.bracket1219 (403343029475724350051441058977999464393/400000000000000000000000000000000000000) (245219220665382282813171303771172767333/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1218 BracketBatch0076.bracket1219
  (403343029475724350051441058977999464393/400000000000000000000000000000000000000) (245219220665382282813171303771172767333/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1218
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1219
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (2019802487868704275211554151484455300413/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2019802487868704275211554151484455300413/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (10130045533363509361976965331813925480341/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10130045533363509361976965331813925480341/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (10114528986353515369017368044618100991203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10114528986353515369017368044618100991203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1219 BracketBatch0076.bracket1220 (10114528986353515369017368044618100991203/10000000000000000000000000000000000000000) (49382725415532598767985614023974249061/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1219 BracketBatch0076.bracket1220
  (10114528986353515369017368044618100991203/10000000000000000000000000000000000000000) (49382725415532598767985614023974249061/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1219
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1220
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (5065022766681754680988482665906962740169/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5065022766681754680988482665906962740169/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (10161239975524899110916645256562057044341/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10161239975524899110916645256562057044341/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (20291285508888408472893610588375982524679/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20291285508888408472893610588375982524679/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1220 BracketBatch0076.bracket1221 (20291285508888408472893610588375982524679/20000000000000000000000000000000000000000) (248619200971319978712622830929761935251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1220 BracketBatch0076.bracket1221
  (20291285508888408472893610588375982524679/20000000000000000000000000000000000000000) (248619200971319978712622830929761935251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1220
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1221
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (5080619987762449555458322628281028522169/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5080619987762449555458322628281028522169/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2548149362152573733454729464248286815187/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2548149362152573733454729464248286815187/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (10176918712067597022367781556777602152543/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10176918712067597022367781556777602152543/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1221 BracketBatch0076.bracket1222 (10176918712067597022367781556777602152543/10000000000000000000000000000000000000000) (250336030561216482950211320055970372373/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1221 BracketBatch0076.bracket1222
  (10176918712067597022367781556777602152543/10000000000000000000000000000000000000000) (250336030561216482950211320055970372373/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1221
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1222
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2038519489722058986763783571398629452149/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2038519489722058986763783571398629452149/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1022411965959353579524979616063459157771/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1022411965959353579524979616063459157771/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (4083343421640766145813742803525547767691/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4083343421640766145813742803525547767691/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1222 BracketBatch0076.bracket1223 (4083343421640766145813742803525547767691/4000000000000000000000000000000000000000) (31508025638766773763295505108566798649/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1222 BracketBatch0076.bracket1223
  (4083343421640766145813742803525547767691/4000000000000000000000000000000000000000) (31508025638766773763295505108566798649/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1222
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1223
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (10224119659593535795249796160634591577707/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10224119659593535795249796160634591577707/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (10255808340079898107470595340450180962893/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10255808340079898107470595340450180962893/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (102399639998367169513601957505423862703/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (102399639998367169513601957505423862703/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0152.rows ScalarLogs0152.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1223 BracketBatch0076.bracket1224 (102399639998367169513601957505423862703/100000000000000000000000000000000000000) (253803814946140943294676408273878298873/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1223 BracketBatch0076.bracket1224
  (102399639998367169513601957505423862703/100000000000000000000000000000000000000) (253803814946140943294676408273878298873/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1223
