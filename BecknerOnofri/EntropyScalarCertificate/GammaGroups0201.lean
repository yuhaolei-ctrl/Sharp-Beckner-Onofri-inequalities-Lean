module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0251
public import BecknerOnofri.EntropyScalarCertificate.Bessel0252
public import BecknerOnofri.EntropyScalarCertificate.Bessel0614
public import BecknerOnofri.EntropyScalarCertificate.Bessel0615
public import BecknerOnofri.EntropyScalarCertificate.Brackets0100
public import BecknerOnofri.EntropyScalarCertificate.Brackets0101
public import BecknerOnofri.EntropyScalarCertificate.Logs0201
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1608
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3746181483580899797237359295617492449581/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3746181483580899797237359295617492449581/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (18742102660948090784572696418230376017447/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18742102660948090784572696418230376017447/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (4684126259856573721344936612039729783169/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4684126259856573721344936612039729783169/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1608 BracketBatch0100.bracket1609 (4684126259856573721344936612039729783169/2500000000000000000000000000000000000000) (367725591347212213767208758621276981753/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1608 BracketBatch0100.bracket1609
  (4684126259856573721344936612039729783169/2500000000000000000000000000000000000000) (367725591347212213767208758621276981753/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1608
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1609
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (4685525665237022696143174104557594004361/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4685525665237022696143174104557594004361/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (9376656640278676599495800579815359665167/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9376656640278676599495800579815359665167/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (18747707970752721991782148788930547673889/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18747707970752721991782148788930547673889/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1609 BracketBatch0100.bracket1610 (18747707970752721991782148788930547673889/10000000000000000000000000000000000000000) (736042848580808767043753534498815305419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1609 BracketBatch0100.bracket1610
  (18747707970752721991782148788930547673889/10000000000000000000000000000000000000000) (736042848580808767043753534498815305419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1609
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1610
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (18753313280557353198991601159630719330331/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18753313280557353198991601159630719330331/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (18764539309956418292805399407079287190313/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18764539309956418292805399407079287190313/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (9379463147628442872949250141677501630161/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9379463147628442872949250141677501630161/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1610 BracketBatch0100.bracket1611 (9379463147628442872949250141677501630161/5000000000000000000000000000000000000000) (736635160062555391099160878571907339503/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1610 BracketBatch0100.bracket1611
  (9379463147628442872949250141677501630161/5000000000000000000000000000000000000000) (736635160062555391099160878571907339503/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1610
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1611
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1876453930995641829280539940707928719031/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1876453930995641829280539940707928719031/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (18775780782460778797191870254583544554083/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18775780782460778797191870254583544554083/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (37540320092417197089997269661662831744393/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37540320092417197089997269661662831744393/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1611 BracketBatch0100.bracket1612 (37540320092417197089997269661662831744393/20000000000000000000000000000000000000000) (92153514769249823621121092592569810881/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1611 BracketBatch0100.bracket1612
  (37540320092417197089997269661662831744393/20000000000000000000000000000000000000000) (92153514769249823621121092592569810881/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1611
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1612
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (117348629890379867482449189091147153463/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117348629890379867482449189091147153463/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1878703773147758938139173872833654733569/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1878703773147758938139173872833654733569/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (3756281851393836817858360898292009188977/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3756281851393836817858360898292009188977/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1612 BracketBatch0100.bracket1613 (3756281851393836817858360898292009188977/2000000000000000000000000000000000000000) (737821723871397836466402851200880047149/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1612 BracketBatch0100.bracket1613
  (3756281851393836817858360898292009188977/2000000000000000000000000000000000000000) (737821723871397836466402851200880047149/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1612
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1613
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (18787037731477589381391738728336547335687/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18787037731477589381391738728336547335687/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (9399155095252984551041724317152529574277/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9399155095252984551041724317152529574277/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0614.rows BesselBatch0614.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (37585347921983558483475187362641606484241/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37585347921983558483475187362641606484241/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1613 BracketBatch0100.bracket1614 (37585347921983558483475187362641606484241/20000000000000000000000000000000000000000) (73841597823294169853217279462104831281/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1613 BracketBatch0100.bracket1614
  (37585347921983558483475187362641606484241/20000000000000000000000000000000000000000) (73841597823294169853217279462104831281/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1613
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1614
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (18798310190505969102083448634305059148551/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18798310190505969102083448634305059148551/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (18809598193137305037433887428828850402491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18809598193137305037433887428828850402491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (18803954191821637069758668031566954775521/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18803954191821637069758668031566954775521/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1614 BracketBatch0100.bracket1615 (18803954191821637069758668031566954775521/10000000000000000000000000000000000000000) (739010882258751741579027223810882805109/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1614 BracketBatch0100.bracket1615
  (18803954191821637069758668031566954775521/10000000000000000000000000000000000000000) (739010882258751741579027223810882805109/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1614
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1615
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (2351199774142163129679235928603606300311/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2351199774142163129679235928603606300311/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (18820901773055557111404727001782441036291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18820901773055557111404727001782441036291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (37630499966192862148838614430611291438779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37630499966192862148838614430611291438779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0201.rows ScalarLogs0201.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0100.bracket1615 BracketBatch0101.bracket1616 (37630499966192862148838614430611291438779/20000000000000000000000000000000000000000) (147921287394177291129350216150332438993/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0100.bracket1615 BracketBatch0101.bracket1616
  (37630499966192862148838614430611291438779/20000000000000000000000000000000000000000) (147921287394177291129350216150332438993/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1615
