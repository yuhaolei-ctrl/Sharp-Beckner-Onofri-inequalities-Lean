module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0227
public import BecknerOnofri.EntropyScalarCertificate.Bessel0228
public import BecknerOnofri.EntropyScalarCertificate.Bessel0602
public import BecknerOnofri.EntropyScalarCertificate.Bessel0603
public import BecknerOnofri.EntropyScalarCertificate.Brackets0091
public import BecknerOnofri.EntropyScalarCertificate.Logs0182
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1456
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4297528366060994856721905511805755454087/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4297528366060994856721905511805755454087/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2149913684544310847318182643820947000749/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2149913684544310847318182643820947000749/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (1719471147029923310271654159889529891117/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1719471147029923310271654159889529891117/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1456 BracketBatch0091.bracket1457 (1719471147029923310271654159889529891117/1000000000000000000000000000000000000000) (652461370524531441943958956437401294861/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1456 BracketBatch0091.bracket1457
  (1719471147029923310271654159889529891117/1000000000000000000000000000000000000000) (652461370524531441943958956437401294861/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1456
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1457
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (17199309476354486778545461150567576005989/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17199309476354486778545461150567576005989/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (537766147539400997823072293744384089003/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (537766147539400997823072293744384089003/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (6881565239523063741776754910077573370817/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6881565239523063741776754910077573370817/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1457 BracketBatch0091.bracket1458 (6881565239523063741776754910077573370817/4000000000000000000000000000000000000000) (65296563543678824179572436544986110417/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1457 BracketBatch0091.bracket1458
  (6881565239523063741776754910077573370817/4000000000000000000000000000000000000000) (65296563543678824179572436544986110417/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1457
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1458
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (17208516721260831930338313399820290848093/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17208516721260831930338313399820290848093/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (8608867610604336347928208581584555865663/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8608867610604336347928208581584555865663/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (34426251942469504626194730562989402579419/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34426251942469504626194730562989402579419/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1458 BracketBatch0091.bracket1459 (34426251942469504626194730562989402579419/20000000000000000000000000000000000000000) (653470412019265495186599298823517070351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1458 BracketBatch0091.bracket1459
  (34426251942469504626194730562989402579419/20000000000000000000000000000000000000000) (653470412019265495186599298823517070351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1458
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1459
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (17217735221208672695856417163169111731323/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17217735221208672695856417163169111731323/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (4306741249625058835675692076592144991663/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4306741249625058835675692076592144991663/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1377788008788356321542367418781507667919/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1377788008788356321542367418781507667919/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1459 BracketBatch0091.bracket1460 (1377788008788356321542367418781507667919/800000000000000000000000000000000000000) (653975701034109828602788208253143366657/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1459 BracketBatch0091.bracket1460
  (1377788008788356321542367418781507667919/800000000000000000000000000000000000000) (653975701034109828602788208253143366657/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1459
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1460
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (17226964998500235342702768306368579966649/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17226964998500235342702768306368579966649/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1077262879718405392346669157848636188039/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1077262879718405392346669157848636188039/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (34463171073994721620249474831946758975273/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34463171073994721620249474831946758975273/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1460 BracketBatch0091.bracket1461 (34463171073994721620249474831946758975273/20000000000000000000000000000000000000000) (32724075162244581504221527228102618719/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1460 BracketBatch0091.bracket1461
  (34463171073994721620249474831946758975273/20000000000000000000000000000000000000000) (32724075162244581504221527228102618719/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1460
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1461
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (17236206075494486277546706525578179008621/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17236206075494486277546706525578179008621/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (34490916949214608673515267348134801297/20000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34490916949214608673515267348134801297/20000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (34481664550101790614304340199645579657121/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34481664550101790614304340199645579657121/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1461 BracketBatch0091.bracket1462 (34481664550101790614304340199645579657121/20000000000000000000000000000000000000000) (163746954854151964030215099752992509869/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1461 BracketBatch0091.bracket1462
  (34481664550101790614304340199645579657121/20000000000000000000000000000000000000000) (163746954854151964030215099752992509869/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1461
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1462
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (17245458474607304336757633674067400648497/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17245458474607304336757633674067400648497/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3450944443662330737022549536305949600193/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3450944443662330737022549536305949600193/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (17250090346459479010935190677798574324731/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17250090346459479010935190677798574324731/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1462 BracketBatch0091.bracket1463 (17250090346459479010935190677798574324731/10000000000000000000000000000000000000000) (131098930063136968811013181766335822039/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1462 BracketBatch0091.bracket1463
  (17250090346459479010935190677798574324731/10000000000000000000000000000000000000000) (131098930063136968811013181766335822039/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1462
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1463
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (8627361109155826842556373840764874000481/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8627361109155826842556373840764874000481/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (17263997329137757325084902055344186437203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17263997329137757325084902055344186437203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (6903743909489882202039529947374786887633/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6903743909489882202039529947374786887633/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0182.rows ScalarLogs0182.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1463 BracketBatch0091.bracket1464 (6903743909489882202039529947374786887633/4000000000000000000000000000000000000000) (164000499177495282503065445995466427183/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1463 BracketBatch0091.bracket1464
  (6903743909489882202039529947374786887633/4000000000000000000000000000000000000000) (164000499177495282503065445995466427183/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1463
