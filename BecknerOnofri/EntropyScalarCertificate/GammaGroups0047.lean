module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0058
public import BecknerOnofri.EntropyScalarCertificate.Bessel0059
public import BecknerOnofri.EntropyScalarCertificate.Bessel0060
public import BecknerOnofri.EntropyScalarCertificate.Bessel0518
public import BecknerOnofri.EntropyScalarCertificate.Brackets0023
public import BecknerOnofri.EntropyScalarCertificate.Brackets0024
public import BecknerOnofri.EntropyScalarCertificate.Logs0047
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0376
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (166073683419879614127959329854638942667/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166073683419879614127959329854638942667/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (266128573627713033153813550953832329599/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266128573627713033153813550953832329599/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (2659232335497602078792742393606273189331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2659232335497602078792742393606273189331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0376 BracketBatch0023.bracket0377 (2659232335497602078792742393606273189331/20000000000000000000000000000000000000000) (117801539133733951816604597760730673/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0376 BracketBatch0023.bracket0377
  (2659232335497602078792742393606273189331/20000000000000000000000000000000000000000) (117801539133733951816604597760730673/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0376
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0377
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (166330358517320645721133469346145205999/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166330358517320645721133469346145205999/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (666348217560455125303410911124447302181/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (666348217560455125303410911124447302181/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1331669651629737708187944788509028126177/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1331669651629737708187944788509028126177/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0377 BracketBatch0023.bracket0378 (1331669651629737708187944788509028126177/10000000000000000000000000000000000000000) (59261272996715378625441336667175789/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0377 BracketBatch0023.bracket0378
  (1331669651629737708187944788509028126177/10000000000000000000000000000000000000000) (59261272996715378625441336667175789/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0377
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0378
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1332696435120910250606821822248894604359/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1332696435120910250606821822248894604359/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (266950033716605383178581503483154926777/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266950033716605383178581503483154926777/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (666861650925984291624932334916167309561/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (666861650925984291624932334916167309561/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0378 BracketBatch0023.bracket0379 (666861650925984291624932334916167309561/5000000000000000000000000000000000000000) (1907949817419563781544345741442173/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0378 BracketBatch0023.bracket0379
  (666861650925984291624932334916167309561/5000000000000000000000000000000000000000) (1907949817419563781544345741442173/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0378
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0379
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (667375084291513457946453758707887316941/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (667375084291513457946453758707887316941/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (133680406880198866471931860476241665707/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (133680406880198866471931860476241665707/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (333944279673126947576528265272273911369/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (333944279673126947576528265272273911369/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0379 BracketBatch0023.bracket0380 (333944279673126947576528265272273911369/2500000000000000000000000000000000000000) (119974502146679938751861988305447449/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0379 BracketBatch0023.bracket0380
  (333944279673126947576528265272273911369/2500000000000000000000000000000000000000) (119974502146679938751861988305447449/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0379
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0380
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1336804068801988664719318604762416657067/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1336804068801988664719318604762416657067/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (669429068027493988489480780180857204453/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (669429068027493988489480780180857204453/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2675662204856976641698280165124131065973/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2675662204856976641698280165124131065973/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0380 BracketBatch0023.bracket0381 (2675662204856976641698280165124131065973/20000000000000000000000000000000000000000) (241410943821949320565478160097797789/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0380 BracketBatch0023.bracket0381
  (2675662204856976641698280165124131065973/20000000000000000000000000000000000000000) (241410943821949320565478160097797789/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0380
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0381
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1338858136054987976978961560361714408903/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1338858136054987976978961560361714408903/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (335228092654834132909714388077653643279/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (335228092654834132909714388077653643279/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (2679770506674324508617819112672328982019/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2679770506674324508617819112672328982019/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0381 BracketBatch0023.bracket0382 (2679770506674324508617819112672328982019/20000000000000000000000000000000000000000) (9715182651350933008091602108545643/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0381 BracketBatch0023.bracket0382
  (2679770506674324508617819112672328982019/20000000000000000000000000000000000000000) (9715182651350933008091602108545643/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0381
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0382
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1340912370619336531638857552310614573113/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1340912370619336531638857552310614573113/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (16787084659655817865276292281718170099/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16787084659655817865276292281718170099/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2683879143391801960860960934848068181033/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2683879143391801960860960934848068181033/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0382 BracketBatch0023.bracket0383 (2683879143391801960860960934848068181033/20000000000000000000000000000000000000000) (244354892232616804637686551526357367/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0382 BracketBatch0023.bracket0383
  (2683879143391801960860960934848068181033/20000000000000000000000000000000000000000) (244354892232616804637686551526357367/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0382
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0383
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1342966772772465429222103382537453607917/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1342966772772465429222103382537453607917/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1345021342791925414499038670813280613319/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1345021342791925414499038670813280613319/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (671997028891097710930285513337683555309/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (671997028891097710930285513337683555309/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0047.rows ScalarLogs0047.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0023.bracket0383 BracketBatch0024.bracket0384 (671997028891097710930285513337683555309/5000000000000000000000000000000000000000) (49167388451100107813386438059502927/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0023.bracket0383 BracketBatch0024.bracket0384
  (671997028891097710930285513337683555309/5000000000000000000000000000000000000000) (49167388451100107813386438059502927/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0383
