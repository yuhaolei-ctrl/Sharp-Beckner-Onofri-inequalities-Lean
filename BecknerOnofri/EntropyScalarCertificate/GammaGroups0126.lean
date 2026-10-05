module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0157
public import BecknerOnofri.EntropyScalarCertificate.Bessel0158
public import BecknerOnofri.EntropyScalarCertificate.Bessel0567
public import BecknerOnofri.EntropyScalarCertificate.Bessel0568
public import BecknerOnofri.EntropyScalarCertificate.Brackets0063
public import BecknerOnofri.EntropyScalarCertificate.Logs0126
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1008
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (5641396496500810704859099985294107412141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5641396496500810704859099985294107412141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (5656768437215468519543248692717221510319/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5656768437215468519543248692717221510319/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (564908246685813961220117433900566446123/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (564908246685813961220117433900566446123/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1008 BracketBatch0063.bracket1009 (564908246685813961220117433900566446123/1000000000000000000000000000000000000000) (50032558164520090526497266274319730657/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1008 BracketBatch0063.bracket1009
  (564908246685813961220117433900566446123/1000000000000000000000000000000000000000) (50032558164520090526497266274319730657/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1008
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1009
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1414192109303867129885812173179305377579/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1414192109303867129885812173179305377579/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1418043208313514998918377847596291793947/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1418043208313514998918377847596291793947/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1416117658808691064402095010387798585763/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1416117658808691064402095010387798585763/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1009 BracketBatch0063.bracket1010 (1416117658808691064402095010387798585763/2500000000000000000000000000000000000000) (50468283147159035477457693603944097943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1009 BracketBatch0063.bracket1010
  (1416117658808691064402095010387798585763/2500000000000000000000000000000000000000) (50468283147159035477457693603944097943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1009
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1010
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1134434566650811999134702278077033435157/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1134434566650811999134702278077033435157/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1421902468869896730066195432174970737551/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1421902468869896730066195432174970737551/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (11359782708733646915938293119085050125989/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11359782708733646915938293119085050125989/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1010 BracketBatch0063.bracket1011 (11359782708733646915938293119085050125989/20000000000000000000000000000000000000000) (10181409383798431372726514575329244983/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1010 BracketBatch0063.bracket1011
  (11359782708733646915938293119085050125989/20000000000000000000000000000000000000000) (10181409383798431372726514575329244983/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1010
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1011
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (5687609875479586920264781728699882950201/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5687609875479586920264781728699882950201/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (5703079756199012084056969771141177935753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5703079756199012084056969771141177935753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (5695344815839299502160875749920530442977/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5695344815839299502160875749920530442977/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1011 BracketBatch0063.bracket1012 (5695344815839299502160875749920530442977/10000000000000000000000000000000000000000) (51348866633103593005199502782290123633/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1011 BracketBatch0063.bracket1012
  (5695344815839299502160875749920530442977/10000000000000000000000000000000000000000) (51348866633103593005199502782290123633/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1011
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1012
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (22812319024796048336227879084564711743/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22812319024796048336227879084564711743/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1429645667294481512355711392034659429417/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1429645667294481512355711392034659429417/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (5710831212688469066739907669639907826709/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5710831212688469066739907669639907826709/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1012 BracketBatch0063.bracket1013 (5710831212688469066739907669639907826709/10000000000000000000000000000000000000000) (51793759535621811376906934576147928213/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1012 BracketBatch0063.bracket1013
  (5710831212688469066739907669639907826709/10000000000000000000000000000000000000000) (51793759535621811376906934576147928213/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1012
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1013
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1143716533835585209884569113627727543533/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1143716533835585209884569113627727543533/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2867059404827697244785559570835139016153/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2867059404827697244785559570835139016153/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (11452701478833320538993964709808915749971/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11452701478833320538993964709808915749971/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1013 BracketBatch0063.bracket1014 (11452701478833320538993964709808915749971/20000000000000000000000000000000000000000) (26120871483219044590367315355191373417/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1013 BracketBatch0063.bracket1014
  (11452701478833320538993964709808915749971/20000000000000000000000000000000000000000) (26120871483219044590367315355191373417/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1013
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1014
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (5734118809655394489571119141670278032303/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5734118809655394489571119141670278032303/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2874844187179494364100763359871394822729/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2874844187179494364100763359871394822729/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (11483807184014383217772645861413067677761/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11483807184014383217772645861413067677761/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1014 BracketBatch0063.bracket1015 (11483807184014383217772645861413067677761/20000000000000000000000000000000000000000) (52692834359933304198596064558228635209/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1014 BracketBatch0063.bracket1015
  (11483807184014383217772645861413067677761/20000000000000000000000000000000000000000) (52692834359933304198596064558228635209/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1014
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1015
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1149937674871797745640305343948557929091/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1149937674871797745640305343948557929091/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1441322890380000538177312218238349171263/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1441322890380000538177312218238349171263/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (11514979935878990880910775592696186330507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11514979935878990880910775592696186330507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0126.rows ScalarLogs0126.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1015 BracketBatch0063.bracket1016 (11514979935878990880910775592696186330507/20000000000000000000000000000000000000000) (13286762811428288651432426356088838751/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1015 BracketBatch0063.bracket1016
  (11514979935878990880910775592696186330507/20000000000000000000000000000000000000000) (13286762811428288651432426356088838751/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1015
