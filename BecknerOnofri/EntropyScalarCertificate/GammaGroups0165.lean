module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0206
public import BecknerOnofri.EntropyScalarCertificate.Bessel0207
public import BecknerOnofri.EntropyScalarCertificate.Bessel0592
public import BecknerOnofri.EntropyScalarCertificate.Brackets0082
public import BecknerOnofri.EntropyScalarCertificate.Brackets0083
public import BecknerOnofri.EntropyScalarCertificate.Logs0165
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1320
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (576726445043233714102078918943363771363/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (576726445043233714102078918943363771363/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (14449241831139612548131849652634402028851/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14449241831139612548131849652634402028851/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (14433701478610227700341911313109248156463/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14433701478610227700341911313109248156463/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1320 BracketBatch0082.bracket1321 (14433701478610227700341911313109248156463/10000000000000000000000000000000000000000) (49526116380098326353203749365086549893/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1320 BracketBatch0082.bracket1321
  (14433701478610227700341911313109248156463/10000000000000000000000000000000000000000) (49526116380098326353203749365086549893/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1320
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1321
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (903077614446225784258240603289650126803/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (903077614446225784258240603289650126803/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (7240234357124585355860943906741092717889/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7240234357124585355860943906741092717889/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (14464855272694391629926868733058293732313/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14464855272694391629926868733058293732313/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1321 BracketBatch0082.bracket1322 (14464855272694391629926868733058293732313/10000000000000000000000000000000000000000) (497045971347605303729913790016650971349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1321 BracketBatch0082.bracket1322
  (14464855272694391629926868733058293732313/10000000000000000000000000000000000000000) (497045971347605303729913790016650971349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1321
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1322
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (579218748569966828468875512539287417431/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (579218748569966828468875512539287417431/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (7255921484916625816584140131728516613209/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7255921484916625816584140131728516613209/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (28992311684082422344890168076939218662193/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28992311684082422344890168076939218662193/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1322 BracketBatch0082.bracket1323 (28992311684082422344890168076939218662193/20000000000000000000000000000000000000000) (498838468859982826139735259944065746979/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1322 BracketBatch0082.bracket1323
  (28992311684082422344890168076939218662193/20000000000000000000000000000000000000000) (498838468859982826139735259944065746979/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1322
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1323
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (2902368593966650326633656052691406645283/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2902368593966650326633656052691406645283/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (454480181413034595740100416788947804221/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (454480181413034595740100416788947804221/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (29055208775050358696851493600703362961487/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29055208775050358696851493600703362961487/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1323 BracketBatch0082.bracket1324 (29055208775050358696851493600703362961487/20000000000000000000000000000000000000000) (50063870532850820882992172286635072997/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1323 BracketBatch0082.bracket1324
  (29055208775050358696851493600703362961487/20000000000000000000000000000000000000000) (50063870532850820882992172286635072997/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1323
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1324
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (14543365805217107063683213337246329735069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14543365805217107063683213337246329735069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (7287519220398154761885304486121703760737/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7287519220398154761885304486121703760737/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (29118404246013416587453822309489737256543/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29118404246013416587453822309489737256543/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1324 BracketBatch0082.bracket1325 (29118404246013416587453822309489737256543/20000000000000000000000000000000000000000) (502446730175869825245171301767019022779/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1324 BracketBatch0082.bracket1325
  (29118404246013416587453822309489737256543/20000000000000000000000000000000000000000) (502446730175869825245171301767019022779/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1324
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1325
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (14575038440796309523770608972243407521471/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14575038440796309523770608972243407521471/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (584274484408324202896988422133042709859/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (584274484408324202896988422133042709859/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (14590950275502207298097659762784737633973/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14590950275502207298097659762784737633973/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1325 BracketBatch0082.bracket1326 (14590950275502207298097659762784737633973/10000000000000000000000000000000000000000) (20170503730457305165160146190270669629/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1325 BracketBatch0082.bracket1326
  (14590950275502207298097659762784737633973/10000000000000000000000000000000000000000) (20170503730457305165160146190270669629/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1325
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1326
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1825857763776013134053088819165758468309/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1825857763776013134053088819165758468309/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (7319419030252679449822641167575441005763/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7319419030252679449822641167575441005763/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (14622850085356731986034996444238474878999/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14622850085356731986034996444238474878999/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1326 BracketBatch0082.bracket1327 (14622850085356731986034996444238474878999/10000000000000000000000000000000000000000) (15815198277676977080801969320495776663/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1326 BracketBatch0082.bracket1327
  (14622850085356731986034996444238474878999/10000000000000000000000000000000000000000) (15815198277676977080801969320495776663/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1326
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1327
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (14638838060505358899645282335150882011523/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14638838060505358899645282335150882011523/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2934193510466627586096634462273651661277/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2934193510466627586096634462273651661277/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (7327451403209624207532113661629785079477/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7327451403209624207532113661629785079477/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0165.rows ScalarLogs0165.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1327 BracketBatch0083.bracket1328 (7327451403209624207532113661629785079477/5000000000000000000000000000000000000000) (126979508948650025072902234873433787181/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1327 BracketBatch0083.bracket1328
  (7327451403209624207532113661629785079477/5000000000000000000000000000000000000000) (126979508948650025072902234873433787181/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1327
