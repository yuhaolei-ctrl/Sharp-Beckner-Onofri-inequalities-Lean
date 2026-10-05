module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0116
public import BecknerOnofri.EntropyScalarCertificate.Bessel0117
public import BecknerOnofri.EntropyScalarCertificate.Bessel0547
public import BecknerOnofri.EntropyScalarCertificate.Brackets0046
public import BecknerOnofri.EntropyScalarCertificate.Brackets0047
public import BecknerOnofri.EntropyScalarCertificate.Logs0093
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0744
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (145018631769310077666860142990093090047/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (145018631769310077666860142990093090047/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (2331126481636184068209640046297787804103/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2331126481636184068209640046297787804103/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (930284917989029062175880466827855448971/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (930284917989029062175880466827855448971/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0744 BracketBatch0046.bracket0745 (930284917989029062175880466827855448971/4000000000000000000000000000000000000000) (51566366180611179172485660883877817/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0744 BracketBatch0046.bracket0745
  (930284917989029062175880466827855448971/4000000000000000000000000000000000000000) (51566366180611179172485660883877817/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0744
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0745
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (23311264816361840682096400462977878041/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23311264816361840682096400462977878041/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1170981374801047929110208345334954057089/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1170981374801047929110208345334954057089/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (2336544615619139963215028368483847959139/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2336544615619139963215028368483847959139/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0745 BracketBatch0046.bracket0746 (2336544615619139963215028368483847959139/10000000000000000000000000000000000000000) (2099995627663939547485440257425848251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0745 BracketBatch0046.bracket0746
  (2336544615619139963215028368483847959139/10000000000000000000000000000000000000000) (2099995627663939547485440257425848251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0745
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0746
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (93678509984083834328816667626796324567/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (93678509984083834328816667626796324567/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2352806957682219172211062938165757085497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2352806957682219172211062938165757085497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (586846213410539378803934953604458149959/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (586846213410539378803934953604458149959/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0746 BracketBatch0046.bracket0747 (586846213410539378803934953604458149959/2500000000000000000000000000000000000000) (2137844339957426608016956191054696497/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0746 BracketBatch0046.bracket0747
  (586846213410539378803934953604458149959/2500000000000000000000000000000000000000) (2137844339957426608016956191054696497/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0746
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0747
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1176403478841109586105531469082878542747/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1176403478841109586105531469082878542747/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1181829575757031591235542886921834064763/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1181829575757031591235542886921834064763/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (235823305459814117734107435600471260751/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (235823305459814117734107435600471260751/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0747 BracketBatch0046.bracket0748 (235823305459814117734107435600471260751/1000000000000000000000000000000000000000) (544051378965273424684487122202725671/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0747 BracketBatch0046.bracket0748
  (235823305459814117734107435600471260751/1000000000000000000000000000000000000000) (544051378965273424684487122202725671/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0747
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0748
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2363659151514063182471085773843668129523/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2363659151514063182471085773843668129523/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (29681492211229327181516506872394813651/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29681492211229327181516506872394813651/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (4738178528412409356992406323635253221603/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4738178528412409356992406323635253221603/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0748 BracketBatch0046.bracket0749 (4738178528412409356992406323635253221603/20000000000000000000000000000000000000000) (2215083912566844313880998436279187943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0748 BracketBatch0046.bracket0749
  (4738178528412409356992406323635253221603/20000000000000000000000000000000000000000) (2215083912566844313880998436279187943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0748
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0749
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2374519376898346174521320549791585092077/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2374519376898346174521320549791585092077/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1192693839900113283149361951449832166143/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1192693839900113283149361951449832166143/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (4759907056698572740820044452691249424363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4759907056698572740820044452691249424363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0749 BracketBatch0046.bracket0750 (4759907056698572740820044452691249424363/20000000000000000000000000000000000000000) (1127242156385455724369996368966524159/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0749 BracketBatch0046.bracket0750
  (4759907056698572740820044452691249424363/20000000000000000000000000000000000000000) (1127242156385455724369996368966524159/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0749
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0750
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (2385387679800226566298723902899664332283/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2385387679800226566298723902899664332283/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (299533013293817816204375160545249263851/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (299533013293817816204375160545249263851/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (4781651786150769095933725187261658443091/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4781651786150769095933725187261658443091/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0750 BracketBatch0046.bracket0751 (4781651786150769095933725187261658443091/20000000000000000000000000000000000000000) (458882304948591087190492989712795297/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0750 BracketBatch0046.bracket0751
  (4781651786150769095933725187261658443091/20000000000000000000000000000000000000000) (458882304948591087190492989712795297/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0750
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0751
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (479252821270108505927000256872398822161/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (479252821270108505927000256872398822161/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1203574351423530149222382119901498821479/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1203574351423530149222382119901498821479/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (4803412809197602828079765524164991753763/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4803412809197602828079765524164991753763/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0093.rows ScalarLogs0093.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0751 BracketBatch0047.bracket0752 (4803412809197602828079765524164991753763/20000000000000000000000000000000000000000) (2334870382395651372868202702984054327/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0751 BracketBatch0047.bracket0752
  (4803412809197602828079765524164991753763/20000000000000000000000000000000000000000) (2334870382395651372868202702984054327/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0751
