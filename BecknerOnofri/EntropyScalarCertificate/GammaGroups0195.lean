module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0243
public import BecknerOnofri.EntropyScalarCertificate.Bessel0244
public import BecknerOnofri.EntropyScalarCertificate.Bessel0245
public import BecknerOnofri.EntropyScalarCertificate.Bessel0610
public import BecknerOnofri.EntropyScalarCertificate.Bessel0611
public import BecknerOnofri.EntropyScalarCertificate.Brackets0097
public import BecknerOnofri.EntropyScalarCertificate.Brackets0098
public import BecknerOnofri.EntropyScalarCertificate.Logs0195
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1560
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1138186842138614317229045327049876758379/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1138186842138614317229045327049876758379/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (4555370998841106475431125643585201211339/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4555370998841106475431125643585201211339/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1821623673479112748869461390356941648971/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1821623673479112748869461390356941648971/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1560 BracketBatch0097.bracket1561 (1821623673479112748869461390356941648971/1000000000000000000000000000000000000000) (353895515259698058298264070345308739471/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1560 BracketBatch0097.bracket1561
  (1821623673479112748869461390356941648971/1000000000000000000000000000000000000000) (353895515259698058298264070345308739471/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1560
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1561
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (18221483995364425901724502574340804845353/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18221483995364425901724502574340804845353/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (18231992400134533834706379112484216280347/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18231992400134533834706379112484216280347/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (364534763954989597364308816868250211257/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (364534763954989597364308816868250211257/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1561 BracketBatch0097.bracket1562 (364534763954989597364308816868250211257/200000000000000000000000000000000000000) (708352863902789958826319773514738075011/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1561 BracketBatch0097.bracket1562
  (364534763954989597364308816868250211257/200000000000000000000000000000000000000) (708352863902789958826319773514738075011/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1561
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1562
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2278999050016816729338297389060527035043/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2278999050016816729338297389060527035043/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (2280314339712433138384824755554536314247/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2280314339712433138384824755554536314247/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0610.rows BesselBatch0610.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (455931338972924986772312214461506334929/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (455931338972924986772312214461506334929/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1562 BracketBatch0097.bracket1563 (455931338972924986772312214461506334929/250000000000000000000000000000000000000) (354457648191675496611589711570708899659/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1562 BracketBatch0097.bracket1563
  (455931338972924986772312214461506334929/250000000000000000000000000000000000000) (354457648191675496611589711570708899659/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1562
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1563
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (18242514717699465107078598044436290513973/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18242514717699465107078598044436290513973/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (18253050977308716905118260658364948500111/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18253050977308716905118260658364948500111/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (9123891423752045503049214675700309753521/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9123891423752045503049214675700309753521/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1563 BracketBatch0097.bracket1564 (9123891423752045503049214675700309753521/5000000000000000000000000000000000000000) (354739164443706908536446903284182224271/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1563 BracketBatch0097.bracket1564
  (9123891423752045503049214675700309753521/5000000000000000000000000000000000000000) (354739164443706908536446903284182224271/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1563
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1564
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (4563262744327179226279565164591237125027/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4563262744327179226279565164591237125027/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (18263601208290221997785323556761508125203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18263601208290221997785323556761508125203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (36516652185598938902903584215126456625311/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36516652185598938902903584215126456625311/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1564 BracketBatch0097.bracket1565 (36516652185598938902903584215126456625311/20000000000000000000000000000000000000000) (710041962343061510853665290088904825723/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1564 BracketBatch0097.bracket1565
  (36516652185598938902903584215126456625311/20000000000000000000000000000000000000000) (710041962343061510853665290088904825723/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1564
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1565
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (45659003020725554994463308891903770313/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45659003020725554994463308891903770313/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (18274165440050600311661900176345525876893/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18274165440050600311661900176345525876893/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (36537766648340822309447223733107034002093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36537766648340822309447223733107034002093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1565 BracketBatch0097.bracket1566 (36537766648340822309447223733107034002093/20000000000000000000000000000000000000000) (177651549420032280567471361043936226989/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1565 BracketBatch0097.bracket1566
  (36537766648340822309447223733107034002093/20000000000000000000000000000000000000000) (177651549420032280567471361043936226989/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1565
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1566
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1827416544005060031166190017634552587689/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1827416544005060031166190017634552587689/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (9142371851037705728106533209963897603979/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9142371851037705728106533209963897603979/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2284931821382875735492185412267082567803/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2284931821382875735492185412267082567803/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1566 BracketBatch0097.bracket1567 (2284931821382875735492185412267082567803/1250000000000000000000000000000000000000) (711171035830207158127336172583011585061/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1566 BracketBatch0097.bracket1567
  (2284931821382875735492185412267082567803/1250000000000000000000000000000000000000) (711171035830207158127336172583011585061/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1566
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1567
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (3656948740415082291242613283985559041591/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3656948740415082291242613283985559041591/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2286917002991176025456053269154017029699/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2286917002991176025456053269154017029699/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (36580079726004819659861492573159931445547/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36580079726004819659861492573159931445547/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0195.rows ScalarLogs0195.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0097.bracket1567 BracketBatch0098.bracket1568 (36580079726004819659861492573159931445547/20000000000000000000000000000000000000000) (71173647772664508408270817617780199429/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0097.bracket1567 BracketBatch0098.bracket1568
  (36580079726004819659861492573159931445547/20000000000000000000000000000000000000000) (71173647772664508408270817617780199429/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1567
