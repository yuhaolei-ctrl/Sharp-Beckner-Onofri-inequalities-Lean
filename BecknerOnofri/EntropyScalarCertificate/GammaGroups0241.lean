module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0301
public import BecknerOnofri.EntropyScalarCertificate.Bessel0302
public import BecknerOnofri.EntropyScalarCertificate.Bessel0639
public import BecknerOnofri.EntropyScalarCertificate.Bessel0640
public import BecknerOnofri.EntropyScalarCertificate.Brackets0120
public import BecknerOnofri.EntropyScalarCertificate.Brackets0121
public import BecknerOnofri.EntropyScalarCertificate.Logs0241
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1928
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (17381750991387545181026283712010400686069/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17381750991387545181026283712010400686069/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (6997117891512485240723484237693896508471/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6997117891512485240723484237693896508471/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (69749091440337516565669988612490283914493/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (69749091440337516565669988612490283914493/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1928 BracketBatch0120.bracket1929 (69749091440337516565669988612490283914493/20000000000000000000000000000000000000000) (708420308983032048686108002626677947831/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1928 BracketBatch0120.bracket1929
  (69749091440337516565669988612490283914493/20000000000000000000000000000000000000000) (708420308983032048686108002626677947831/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1928
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1929
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2186599341097651637726088824279342658897/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2186599341097651637726088824279342658897/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (35210709231789924981430682678220189859487/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35210709231789924981430682678220189859487/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (70196298689352351185048103866689672401839/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (70196298689352351185048103866689672401839/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1929 BracketBatch0120.bracket1930 (70196298689352351185048103866689672401839/20000000000000000000000000000000000000000) (1424406399622855479953330142627006071951/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1929 BracketBatch0120.bracket1930
  (70196298689352351185048103866689672401839/20000000000000000000000000000000000000000) (1424406399622855479953330142627006071951/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1929
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1930
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (8802677307947481245357670669555047464871/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8802677307947481245357670669555047464871/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (17719461468978216817157090110132774494107/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17719461468978216817157090110132774494107/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (35324816084873179307872431449242869423849/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35324816084873179307872431449242869423849/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1930 BracketBatch0120.bracket1931 (35324816084873179307872431449242869423849/10000000000000000000000000000000000000000) (1432033195950483966079108826624243375389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1930 BracketBatch0120.bracket1931
  (35324816084873179307872431449242869423849/10000000000000000000000000000000000000000) (1432033195950483966079108826624243375389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1930
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1931
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (35438922937956433634314180220265548988211/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35438922937956433634314180220265548988211/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (445878673701448601122638605525072397097/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (445878673701448601122638605525072397097/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (71109216834072321724125268662271340755971/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (71109216834072321724125268662271340755971/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1931 BracketBatch0120.bracket1932 (71109216834072321724125268662271340755971/20000000000000000000000000000000000000000) (179965220040463610399471900418941791687/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1931 BracketBatch0120.bracket1932
  (71109216834072321724125268662271340755971/20000000000000000000000000000000000000000) (179965220040463610399471900418941791687/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1931
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1932
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (35670293896115888089811088442005791767757/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35670293896115888089811088442005791767757/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (35904887172297580300617942680533586025207/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35904887172297580300617942680533586025207/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (17893795267103367097607257780634844448241/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17893795267103367097607257780634844448241/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1932 BracketBatch0120.bracket1933 (17893795267103367097607257780634844448241/5000000000000000000000000000000000000000) (3618682151899990967956574040856465183/25000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1932 BracketBatch0120.bracket1933
  (17893795267103367097607257780634844448241/5000000000000000000000000000000000000000) (3618682151899990967956574040856465183/25000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1932
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1933
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (8976221793074395075154485670133396506301/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8976221793074395075154485670133396506301/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (36142769639357564846006046213700403805873/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36142769639357564846006046213700403805873/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (72047656811655145146623988894233989831077/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (72047656811655145146623988894233989831077/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1933 BracketBatch0120.bracket1934 (72047656811655145146623988894233989831077/20000000000000000000000000000000000000000) (181910910038986858977516945030113247723/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1933 BracketBatch0120.bracket1934
  (72047656811655145146623988894233989831077/20000000000000000000000000000000000000000) (181910910038986858977516945030113247723/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1933
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1934
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (3614276963935756484600604621370040380587/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3614276963935756484600604621370040380587/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (36384010040379803917483839110084917771791/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36384010040379803917483839110084917771791/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (72526779679737368763489885323785321577661/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (72526779679737368763489885323785321577661/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1934 BracketBatch0120.bracket1935 (72526779679737368763489885323785321577661/20000000000000000000000000000000000000000) (731582908735640961659105951049324360301/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1934 BracketBatch0120.bracket1935
  (72526779679737368763489885323785321577661/20000000000000000000000000000000000000000) (731582908735640961659105951049324360301/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1934
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1935
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (9096002510094950979370959777521229442947/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9096002510094950979370959777521229442947/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (9157169763688084306663722438803434298821/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9157169763688084306663722438803434298821/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2281646534222879410754335277040582967721/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2281646534222879410754335277040582967721/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0241.rows ScalarLogs0241.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1935 BracketBatch0121.bracket1936 (2281646534222879410754335277040582967721/625000000000000000000000000000000000000) (1471109286585873128709084012732470240677/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1935 BracketBatch0121.bracket1936
  (2281646534222879410754335277040582967721/625000000000000000000000000000000000000) (1471109286585873128709084012732470240677/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1935
