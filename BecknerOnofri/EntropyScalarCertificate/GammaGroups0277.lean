module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0346
public import BecknerOnofri.EntropyScalarCertificate.Bessel0347
public import BecknerOnofri.EntropyScalarCertificate.Bessel0662
public import BecknerOnofri.EntropyScalarCertificate.Brackets0138
public import BecknerOnofri.EntropyScalarCertificate.Brackets0139
public import BecknerOnofri.EntropyScalarCertificate.Logs0277
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2216
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (96722550255230706927814051754304844122229/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (96722550255230706927814051754304844122229/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (97087927195194864732809817039591950472321/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (97087927195194864732809817039591950472321/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (3876209549008511433212477375877935891891/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3876209549008511433212477375877935891891/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2216 BracketBatch0138.bracket2217 (3876209549008511433212477375877935891891/400000000000000000000000000000000000000) (2719965840190194793792630785190417826083/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2216 BracketBatch0138.bracket2217
  (3876209549008511433212477375877935891891/400000000000000000000000000000000000000) (2719965840190194793792630785190417826083/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2216
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2217
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (48543963597597432366404908519795975236159/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48543963597597432366404908519795975236159/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (48728058260856908153817088861256771913273/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48728058260856908153817088861256771913273/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (12159002732306792565027749672631593393679/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12159002732306792565027749672631593393679/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2217 BracketBatch0138.bracket2218 (12159002732306792565027749672631593393679/1250000000000000000000000000000000000000) (2724942568788070445241679444161014927381/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2217 BracketBatch0138.bracket2218
  (12159002732306792565027749672631593393679/1250000000000000000000000000000000000000) (2724942568788070445241679444161014927381/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2217
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2218
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (97456116521713816307634177722513543826543/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (97456116521713816307634177722513543826543/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2445678770224752182313400781627886154111/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2445678770224752182313400781627886154111/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (195283267330703903600170208987628989990983/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (195283267330703903600170208987628989990983/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2218 BracketBatch0138.bracket2219 (195283267330703903600170208987628989990983/20000000000000000000000000000000000000000) (2729939877510714708126083246290155472549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2218 BracketBatch0138.bracket2219
  (195283267330703903600170208987628989990983/20000000000000000000000000000000000000000) (2729939877510714708126083246290155472549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2218
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2219
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (97827150808990087292536031265115446164437/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (97827150808990087292536031265115446164437/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (24550265784064029980382911802401411791077/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24550265784064029980382911802401411791077/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (39205642789049241442813535694944218665749/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39205642789049241442813535694944218665749/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2219 BracketBatch0138.bracket2220 (39205642789049241442813535694944218665749/4000000000000000000000000000000000000000) (1367478962416528317587499953319669790491/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2219 BracketBatch0138.bracket2220
  (39205642789049241442813535694944218665749/4000000000000000000000000000000000000000) (1367478962416528317587499953319669790491/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2219
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2220
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (19640212627251223984306329441921129432861/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19640212627251223984306329441921129432861/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (12322235887199968053490250330418601611393/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12322235887199968053490250330418601611393/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (196778950233855864349453649852954460055449/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (196778950233855864349453649852954460055449/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2220 BracketBatch0138.bracket2221 (196778950233855864349453649852954460055449/20000000000000000000000000000000000000000) (2739996870986104189917125319915921724717/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2220 BracketBatch0138.bracket2221
  (196778950233855864349453649852954460055449/20000000000000000000000000000000000000000) (2739996870986104189917125319915921724717/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2220
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2221
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (98577887097599744427922002643348812891141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98577887097599744427922002643348812891141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (98957656812019935019975785683507549981217/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (98957656812019935019975785683507549981217/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (98767771954809839723948894163428181436179/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (98767771954809839723948894163428181436179/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2221 BracketBatch0138.bracket2222 (98767771954809839723948894163428181436179/10000000000000000000000000000000000000000) (2745056877981434581286607134053100043807/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2221 BracketBatch0138.bracket2222
  (98767771954809839723948894163428181436179/10000000000000000000000000000000000000000) (2745056877981434581286607134053100043807/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2221
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2222
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (49478828406009967509987892841753774990607/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49478828406009967509987892841753774990607/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (12417550866714896495393767666920886125913/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12417550866714896495393767666920886125913/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (99149031872869553491562963509437319494259/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (99149031872869553491562963509437319494259/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2222 BracketBatch0138.bracket2223 (99149031872869553491562963509437319494259/10000000000000000000000000000000000000000) (343767263704509679662449229711896637761/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2222 BracketBatch0138.bracket2223
  (99149031872869553491562963509437319494259/10000000000000000000000000000000000000000) (343767263704509679662449229711896637761/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2222
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2223
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (99340406933719171963150141335367089007301/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (99340406933719171963150141335367089007301/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (99726172662638930408742409431599220670127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (99726172662638930408742409431599220670127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (49766644899089525592973137691741577419357/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (49766644899089525592973137691741577419357/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0277.rows ScalarLogs0277.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2223 BracketBatch0139.bracket2224 (49766644899089525592973137691741577419357/5000000000000000000000000000000000000000) (1377620365798898629877072238300384413451/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2223 BracketBatch0139.bracket2224
  (49766644899089525592973137691741577419357/5000000000000000000000000000000000000000) (1377620365798898629877072238300384413451/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2223
