module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0272
public import BecknerOnofri.EntropyScalarCertificate.Bessel0273
public import BecknerOnofri.EntropyScalarCertificate.Bessel0625
public import BecknerOnofri.EntropyScalarCertificate.Brackets0109
public import BecknerOnofri.EntropyScalarCertificate.Logs0218
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1744
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (10204802379141644305799999716359503458419/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10204802379141644305799999716359503458419/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (10211619126961330172767848224284153374761/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10211619126961330172767848224284153374761/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1020821075305148723928392397032182841659/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1020821075305148723928392397032182841659/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1744 BracketBatch0109.bracket1745 (1020821075305148723928392397032182841659/500000000000000000000000000000000000000) (822287957564680967847603886244195625629/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1744 BracketBatch0109.bracket1745
  (1020821075305148723928392397032182841659/500000000000000000000000000000000000000) (822287957564680967847603886244195625629/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1744
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1745
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (20423238253922660345535696448568306749519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20423238253922660345535696448568306749519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (204368926251875475829388902199941935029/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (204368926251875475829388902199941935029/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (40860130879110207928474586668562500252419/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40860130879110207928474586668562500252419/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1745 BracketBatch0109.bracket1746 (40860130879110207928474586668562500252419/20000000000000000000000000000000000000000) (82297758242523471800000863309090256723/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1745 BracketBatch0109.bracket1746
  (40860130879110207928474586668562500252419/20000000000000000000000000000000000000000) (82297758242523471800000863309090256723/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1745
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1746
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (20436892625187547582938890219994193502897/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20436892625187547582938890219994193502897/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (2045056792106511131730903971159712512509/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2045056792106511131730903971159712512509/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (40887460546252658900247929931591318627987/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40887460546252658900247929931591318627987/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1746 BracketBatch0109.bracket1747 (40887460546252658900247929931591318627987/20000000000000000000000000000000000000000) (823668010257839720479501422474870092989/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1746 BracketBatch0109.bracket1747
  (40887460546252658900247929931591318627987/20000000000000000000000000000000000000000) (823668010257839720479501422474870092989/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1746
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1747
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (20450567921065111317309039711597125125087/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20450567921065111317309039711597125125087/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1279016511918028864450836379857484810173/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1279016511918028864450836379857484810173/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (8182966422350714629704484357863376417571/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8182966422350714629704484357863376417571/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1747 BracketBatch0109.bracket1748 (8182966422350714629704484357863376417571/4000000000000000000000000000000000000000) (51522452648707096759048119176612564361/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1747 BracketBatch0109.bracket1748
  (8182966422350714629704484357863376417571/4000000000000000000000000000000000000000) (51522452648707096759048119176612564361/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1747
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1748
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (4092852838137692366242676415543951392553/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4092852838137692366242676415543951392553/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (4095596296667437520947617135151187798207/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4095596296667437520947617135151187798207/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (204711228370128247179757338767378479769/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (204711228370128247179757338767378479769/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1748 BracketBatch0109.bracket1749 (204711228370128247179757338767378479769/100000000000000000000000000000000000000) (20626282002726146358886815117604565699/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1748 BracketBatch0109.bracket1749
  (204711228370128247179757338767378479769/100000000000000000000000000000000000000) (20626282002726146358886815117604565699/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1748
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1749
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (2559747685417148450592260709469492373879/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2559747685417148450592260709469492373879/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (5122929962109471639006556787331911010953/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5122929962109471639006556787331911010953/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (10242425332943768540191078206270895758711/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10242425332943768540191078206270895758711/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1749 BracketBatch0109.bracket1750 (10242425332943768540191078206270895758711/5000000000000000000000000000000000000000) (412872062384502129873767381621623948419/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1749 BracketBatch0109.bracket1750
  (10242425332943768540191078206270895758711/5000000000000000000000000000000000000000) (412872062384502129873767381621623948419/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1749
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1750
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (20491719848437886556026227149327644043809/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20491719848437886556026227149327644043809/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (20505479335564699626422799785820465678289/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20505479335564699626422799785820465678289/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (20498599592001293091224513467574054861049/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20498599592001293091224513467574054861049/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1750 BracketBatch0109.bracket1751 (20498599592001293091224513467574054861049/10000000000000000000000000000000000000000) (51652361105233766284524674354094840343/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1750 BracketBatch0109.bracket1751
  (20498599592001293091224513467574054861049/10000000000000000000000000000000000000000) (51652361105233766284524674354094840343/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1750
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1751
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (10252739667782349813211399892910232839143/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10252739667782349813211399892910232839143/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (10259629997219923361413105019127826688601/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10259629997219923361413105019127826688601/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (320505776015660518353507889250594680121/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (320505776015660518353507889250594680121/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0218.rows ScalarLogs0218.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1751 BracketBatch0109.bracket1752 (320505776015660518353507889250594680121/156250000000000000000000000000000000000) (413566120090197579300028689903830996101/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1751 BracketBatch0109.bracket1752
  (320505776015660518353507889250594680121/156250000000000000000000000000000000000) (413566120090197579300028689903830996101/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1751
