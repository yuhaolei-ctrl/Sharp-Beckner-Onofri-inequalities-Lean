module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0247
public import BecknerOnofri.EntropyScalarCertificate.Bessel0248
public import BecknerOnofri.EntropyScalarCertificate.Bessel0612
public import BecknerOnofri.EntropyScalarCertificate.Bessel0613
public import BecknerOnofri.EntropyScalarCertificate.Brackets0099
public import BecknerOnofri.EntropyScalarCertificate.Logs0198
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1584
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (18466749746136052605229365786384164081781/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18466749746136052605229365786384164081781/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1847758568647941359922135360103816474981/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1847758568647941359922135360103816474981/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (36944335432615466204450719387422328831591/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36944335432615466204450719387422328831591/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1584 BracketBatch0099.bracket1585 (36944335432615466204450719387422328831591/20000000000000000000000000000000000000000) (721442276168753055137926057780307957953/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1584 BracketBatch0099.bracket1585
  (36944335432615466204450719387422328831591/20000000000000000000000000000000000000000) (721442276168753055137926057780307957953/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1584
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1585
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (18477585686479413599221353601038164749807/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18477585686479413599221353601038164749807/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (4622109058163584080472291541780078641721/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4622109058163584080472291541780078641721/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (36966021919133749921110519768158479316691/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36966021919133749921110519768158479316691/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1585 BracketBatch0099.bracket1586 (36966021919133749921110519768158479316691/20000000000000000000000000000000000000000) (722018747128797497044378691932194798853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1585 BracketBatch0099.bracket1586
  (36966021919133749921110519768158479316691/20000000000000000000000000000000000000000) (722018747128797497044378691932194798853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1585
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1586
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (18488436232654336321889166167120314566881/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18488436232654336321889166167120314566881/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (3699860283155941305800338059023512743719/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3699860283155941305800338059023512743719/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (9246934412108510712722714115559469571369/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9246934412108510712722714115559469571369/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1586 BracketBatch0099.bracket1587 (9246934412108510712722714115559469571369/5000000000000000000000000000000000000000) (144519167981551453786852625678513495571/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1586 BracketBatch0099.bracket1587
  (9246934412108510712722714115559469571369/5000000000000000000000000000000000000000) (144519167981551453786852625678513495571/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1586
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1587
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (289051584621557914515651410861211933103/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (289051584621557914515651410861211933103/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (92550906335294400015323505357652334001/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (92550906335294400015323505357652334001/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (4626185335354823316508298920831003814849/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4626185335354823316508298920831003814849/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1587 BracketBatch0099.bracket1588 (4626185335354823316508298920831003814849/2500000000000000000000000000000000000000) (723173555474908390165872722227530422329/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1587 BracketBatch0099.bracket1588
  (4626185335354823316508298920831003814849/2500000000000000000000000000000000000000) (723173555474908390165872722227530422329/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1587
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1588
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (18510181267058880003064701071530466800197/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18510181267058880003064701071530466800197/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (18521075817779957110744958638584039973261/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18521075817779957110744958638584039973261/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (18515628542419418556904829855057253386729/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18515628542419418556904829855057253386729/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1588 BracketBatch0099.bracket1589 (18515628542419418556904829855057253386729/10000000000000000000000000000000000000000) (723751894801361213823383733071634366641/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1588 BracketBatch0099.bracket1589
  (18515628542419418556904829855057253386729/10000000000000000000000000000000000000000) (723751894801361213823383733071634366641/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1588
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1589
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (9260537908889978555372479319292019986629/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9260537908889978555372479319292019986629/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1853198509931605841518060067176719163701/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1853198509931605841518060067176719163701/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (9263265229274003881481389827587807902567/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9263265229274003881481389827587807902567/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1589 BracketBatch0099.bracket1590 (9263265229274003881481389827587807902567/5000000000000000000000000000000000000000) (724330858860064108584641326155667708141/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1589 BracketBatch0099.bracket1590
  (9263265229274003881481389827587807902567/5000000000000000000000000000000000000000) (724330858860064108584641326155667708141/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1589
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1590
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (18531985099316058415180600671767191637007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18531985099316058415180600671767191637007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (927145457156280067401505700410618651881/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (927145457156280067401505700410618651881/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (37074894242441659763210714679979564674627/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37074894242441659763210714679979564674627/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1590 BracketBatch0099.bracket1591 (37074894242441659763210714679979564674627/20000000000000000000000000000000000000000) (362455224312903574648882139632929934447/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1590 BracketBatch0099.bracket1591
  (37074894242441659763210714679979564674627/20000000000000000000000000000000000000000) (362455224312903574648882139632929934447/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1590
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1591
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (18542909143125601348030114008212373037617/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18542909143125601348030114008212373037617/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (18553847980752577946139054561034823529639/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18553847980752577946139054561034823529639/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (4637094640484772411771146071155899570907/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4637094640484772411771146071155899570907/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0198.rows ScalarLogs0198.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1591 BracketBatch0099.bracket1592 (4637094640484772411771146071155899570907/2500000000000000000000000000000000000000) (181372666268806454076621929429666123041/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1591 BracketBatch0099.bracket1592
  (4637094640484772411771146071155899570907/2500000000000000000000000000000000000000) (181372666268806454076621929429666123041/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1591
