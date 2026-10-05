module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0183
public import BecknerOnofri.EntropyScalarCertificate.Bessel0184
public import BecknerOnofri.EntropyScalarCertificate.Bessel0185
public import BecknerOnofri.EntropyScalarCertificate.Bessel0580
public import BecknerOnofri.EntropyScalarCertificate.Bessel0581
public import BecknerOnofri.EntropyScalarCertificate.Brackets0073
public import BecknerOnofri.EntropyScalarCertificate.Brackets0074
public import BecknerOnofri.EntropyScalarCertificate.Logs0147
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1176
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (556044896885975469882618973846939260013/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (556044896885975469882618973846939260013/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (2230530431970505167282277327357141024493/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2230530431970505167282277327357141024493/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (890942003902881409362550644548979612909/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (890942003902881409362550644548979612909/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1176 BracketBatch0073.bracket1177 (890942003902881409362550644548979612909/1000000000000000000000000000000000000000) (183123705202882741234637636468508234307/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1176 BracketBatch0073.bracket1177
  (890942003902881409362550644548979612909/1000000000000000000000000000000000000000) (183123705202882741234637636468508234307/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1176
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1177
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (8922121727882020669129109309428564097969/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8922121727882020669129109309428564097969/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (279613499813668426060429247082895541513/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (279613499813668426060429247082895541513/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (3573950744383882060612569043216244285277/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3573950744383882060612569043216244285277/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1177 BracketBatch0073.bracket1178 (3573950744383882060612569043216244285277/4000000000000000000000000000000000000000) (184416407842197481591574304651943713279/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1177 BracketBatch0073.bracket1178
  (3573950744383882060612569043216244285277/4000000000000000000000000000000000000000) (184416407842197481591574304651943713279/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1177
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1178
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (8947631994037389633933735906652657328413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8947631994037389633933735906652657328413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (112165626283884394942158272509374890107/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (112165626283884394942158272509374890107/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (17920882096748141229306397707402648536973/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17920882096748141229306397707402648536973/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1178 BracketBatch0073.bracket1179 (17920882096748141229306397707402648536973/20000000000000000000000000000000000000000) (185717307463340090742015617296352316169/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1178 BracketBatch0073.bracket1179
  (17920882096748141229306397707402648536973/20000000000000000000000000000000000000000) (185717307463340090742015617296352316169/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1178
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1179
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (8973250102710751595372661800749991208557/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8973250102710751595372661800749991208557/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4499488509866104820769868034969752262351/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4499488509866104820769868034969752262351/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (17972227122442961236912397870689495733259/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17972227122442961236912397870689495733259/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1179 BracketBatch0073.bracket1180 (17972227122442961236912397870689495733259/20000000000000000000000000000000000000000) (23378307459723631696267194067891728917/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1179 BracketBatch0073.bracket1180
  (17972227122442961236912397870689495733259/20000000000000000000000000000000000000000) (23378307459723631696267194067891728917/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1179
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1180
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (8998977019732209641539736069939504524699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8998977019732209641539736069939504524699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (9024813722878528762543344139749315920549/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9024813722878528762543344139749315920549/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (281621730353292787563798128276387819457/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (281621730353292787563798128276387819457/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1180 BracketBatch0073.bracket1181 (281621730353292787563798128276387819457/312500000000000000000000000000000000000) (37668784126229279708555617692862145019/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1180 BracketBatch0073.bracket1181
  (281621730353292787563798128276387819457/312500000000000000000000000000000000000) (37668784126229279708555617692862145019/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1180
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1181
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (4512406861439264381271672069874657960273/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4512406861439264381271672069874657960273/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (9050761202062258489654407410022566203057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9050761202062258489654407410022566203057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (18075574924940787252197751549771882123603/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18075574924940787252197751549771882123603/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1181 BracketBatch0073.bracket1182 (18075574924940787252197751549771882123603/20000000000000000000000000000000000000000) (94834873505326881818600343827211911857/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1181 BracketBatch0073.bracket1182
  (18075574924940787252197751549771882123603/20000000000000000000000000000000000000000) (94834873505326881818600343827211911857/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1181
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1182
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (4525380601031129244827203705011283101527/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4525380601031129244827203705011283101527/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (4538410229762230015688695234688011209913/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4538410229762230015688695234688011209913/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (113297385384916990756448736746241178893/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (113297385384916990756448736746241178893/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1182 BracketBatch0073.bracket1183 (113297385384916990756448736746241178893/125000000000000000000000000000000000000) (191003996052840007742711546642230469581/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1182 BracketBatch0073.bracket1183
  (113297385384916990756448736746241178893/125000000000000000000000000000000000000) (191003996052840007742711546642230469581/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1182
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1183
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (9076820459524460031377390469376022419823/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9076820459524460031377390469376022419823/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (9102992510031117706858632148718829400543/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9102992510031117706858632148718829400543/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (9089906484777788869118011309047425910183/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9089906484777788869118011309047425910183/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0147.rows ScalarLogs0147.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1183 BracketBatch0074.bracket1184 (9089906484777788869118011309047425910183/10000000000000000000000000000000000000000) (192346725551302979676814607045432492353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1183 BracketBatch0074.bracket1184
  (9089906484777788869118011309047425910183/10000000000000000000000000000000000000000) (192346725551302979676814607045432492353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1183
