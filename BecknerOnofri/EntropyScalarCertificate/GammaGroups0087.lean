module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0108
public import BecknerOnofri.EntropyScalarCertificate.Bessel0109
public import BecknerOnofri.EntropyScalarCertificate.Bessel0110
public import BecknerOnofri.EntropyScalarCertificate.Bessel0543
public import BecknerOnofri.EntropyScalarCertificate.Brackets0043
public import BecknerOnofri.EntropyScalarCertificate.Brackets0044
public import BecknerOnofri.EntropyScalarCertificate.Logs0087
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0696
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (997858180924244394919537982133989242319/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (997858180924244394919537982133989242319/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (499459456833026067174886554069982900183/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (499459456833026067174886554069982900183/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (399355418918059305853862218054791008537/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (399355418918059305853862218054791008537/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0696 BracketBatch0043.bracket0697 (399355418918059305853862218054791008537/2000000000000000000000000000000000000000) (1160198352781059715364307340911422437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0696 BracketBatch0043.bracket0697
  (399355418918059305853862218054791008537/2000000000000000000000000000000000000000) (1160198352781059715364307340911422437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0696
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0697
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1997837827332104268699546216279931600729/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1997837827332104268699546216279931600729/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1999959555009219683428972839809478522383/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1999959555009219683428972839809478522383/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (499724672792665494016064882011176265389/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (499724672792665494016064882011176265389/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0697 BracketBatch0043.bracket0698 (499724672792665494016064882011176265389/2500000000000000000000000000000000000000) (291246932579668715646855114463276339/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0697 BracketBatch0043.bracket0698
  (499724672792665494016064882011176265389/2500000000000000000000000000000000000000) (291246932579668715646855114463276339/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0697
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0698
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (99997977750460984171448641990473926119/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (99997977750460984171448641990473926119/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (2002081545207464967555232081968025744403/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2002081545207464967555232081968025744403/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (4002041100216684650984204921777504266783/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4002041100216684650984204921777504266783/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0698 BracketBatch0043.bracket0699 (4002041100216684650984204921777504266783/20000000000000000000000000000000000000000) (584896016870253644549080795742269267/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0698 BracketBatch0043.bracket0699
  (4002041100216684650984204921777504266783/20000000000000000000000000000000000000000) (584896016870253644549080795742269267/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0698
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0699
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (5005203863018662418888080204920064361/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5005203863018662418888080204920064361/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (2004203798254673259840175220091654000223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2004203798254673259840175220091654000223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (4006285343462138227395407302059679744623/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4006285343462138227395407302059679744623/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0699 BracketBatch0043.bracket0700 (4006285343462138227395407302059679744623/20000000000000000000000000000000000000000) (1174611294766143298618579294224041129/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0699 BracketBatch0043.bracket0700
  (4006285343462138227395407302059679744623/20000000000000000000000000000000000000000) (1174611294766143298618579294224041129/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0699
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0700
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (100210189912733662992008761004582700011/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (100210189912733662992008761004582700011/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2006326314478881220289723653031253924679/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2006326314478881220289723653031253924679/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (4010530112733554480129898873122907924899/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4010530112733554480129898873122907924899/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0700 BracketBatch0043.bracket0701 (4010530112733554480129898873122907924899/20000000000000000000000000000000000000000) (1179445545152768776681050840129011611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0700 BracketBatch0043.bracket0701
  (4010530112733554480129898873122907924899/20000000000000000000000000000000000000000) (1179445545152768776681050840129011611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0700
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0701
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (501581578619720305072430913257813481169/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (501581578619720305072430913257813481169/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (2008449094208329346560611912996713641379/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2008449094208329346560611912996713641379/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (802955081737442113370067113205593513211/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (802955081737442113370067113205593513211/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0701 BracketBatch0043.bracket0702 (802955081737442113370067113205593513211/4000000000000000000000000000000000000000) (1184294816695186624520705082416159557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0701 BracketBatch0043.bracket0702
  (802955081737442113370067113205593513211/4000000000000000000000000000000000000000) (1184294816695186624520705082416159557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0701
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0702
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (62764034194010292080019122281147301293/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62764034194010292080019122281147301293/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2010572137771462290764551409632823695691/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2010572137771462290764551409632823695691/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (4019021231979791637325163322629537337067/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4019021231979791637325163322629537337067/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0702 BracketBatch0043.bracket0703 (4019021231979791637325163322629537337067/20000000000000000000000000000000000000000) (1189159141225834218611321300693842071/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0702 BracketBatch0043.bracket0703
  (4019021231979791637325163322629537337067/20000000000000000000000000000000000000000) (1189159141225834218611321300693842071/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0702
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0703
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0109.rows BesselBatch0109.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (251321517221432786345568926204102961961/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (251321517221432786345568926204102961961/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (503173861374232294167647294651947451379/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (503173861374232294167647294651947451379/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1005816895817097866858785147060153375301/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1005816895817097866858785147060153375301/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0087.rows ScalarLogs0087.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0703 BracketBatch0044.bracket0704 (1005816895817097866858785147060153375301/5000000000000000000000000000000000000000) (59701927530740044793674971809091683/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0703 BracketBatch0044.bracket0704
  (1005816895817097866858785147060153375301/5000000000000000000000000000000000000000) (59701927530740044793674971809091683/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0703
