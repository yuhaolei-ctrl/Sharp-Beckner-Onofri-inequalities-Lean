import BecknerOnofri.EntropyScalarCertificate.Bessel0258
import BecknerOnofri.EntropyScalarCertificate.Bessel0259
import BecknerOnofri.EntropyScalarCertificate.Bessel0260
import BecknerOnofri.EntropyScalarCertificate.Bessel0618
import BecknerOnofri.EntropyScalarCertificate.Brackets0103
import BecknerOnofri.EntropyScalarCertificate.Brackets0104
import BecknerOnofri.EntropyScalarCertificate.Logs0207
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1656
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (9643108401188464340252650317092238529449/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9643108401188464340252650317092238529449/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (4824547309569614442608904278140041265263/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4824547309569614442608904278140041265263/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (771688120813107729018818354934892842399/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (771688120813107729018818354934892842399/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1656 BracketBatch0103.bracket1657 (771688120813107729018818354934892842399/400000000000000000000000000000000000000) (382298651072059766360642282561555825693/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1656 BracketBatch0103.bracket1657
  (771688120813107729018818354934892842399/400000000000000000000000000000000000000) (382298651072059766360642282561555825693/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1656
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1657
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (19298189238278457770435617112560165061049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19298189238278457770435617112560165061049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (120688617212555852699770946117398981733/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (120688617212555852699770946117398981733/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (38608367992287394202398968491344002138329/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38608367992287394202398968491344002138329/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1657 BracketBatch0103.bracket1658 (38608367992287394202398968491344002138329/20000000000000000000000000000000000000000) (95652641856462912505978489621965991157/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1657 BracketBatch0103.bracket1658
  (38608367992287394202398968491344002138329/20000000000000000000000000000000000000000) (95652641856462912505978489621965991157/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1657
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1658
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (19310178754008936431963351378783837077277/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19310178754008936431963351378783837077277/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (19322185387539171858494455705702766661841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19322185387539171858494455705702766661841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (19316182070774054145228903542243301869559/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19316182070774054145228903542243301869559/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1658 BracketBatch0103.bracket1659 (19316182070774054145228903542243301869559/10000000000000000000000000000000000000000) (765845664083792277328298994538221528673/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1658 BracketBatch0103.bracket1659
  (19316182070774054145228903542243301869559/10000000000000000000000000000000000000000) (765845664083792277328298994538221528673/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1658
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1659
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (9661092693769585929247227852851383330919/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9661092693769585929247227852851383330919/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (19334209176947225390113499395194029437069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19334209176947225390113499395194029437069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (38656394564486397248607955100896796098907/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38656394564486397248607955100896796098907/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1659 BracketBatch0103.bracket1660 (38656394564486397248607955100896796098907/20000000000000000000000000000000000000000) (766470890951710809398551802010775090701/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1659 BracketBatch0103.bracket1660
  (38656394564486397248607955100896796098907/20000000000000000000000000000000000000000) (766470890951710809398551802010775090701/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1659
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1660
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (9667104588473612695056749697597014718533/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9667104588473612695056749697597014718533/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (19346250160418777226895473487475953335311/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19346250160418777226895473487475953335311/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (38680459337366002617008972882669982772377/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38680459337366002617008972882669982772377/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1660 BracketBatch0103.bracket1661 (38680459337366002617008972882669982772377/20000000000000000000000000000000000000000) (767096816568907683623560719603606277097/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1660 BracketBatch0103.bracket1661
  (38680459337366002617008972882669982772377/20000000000000000000000000000000000000000) (767096816568907683623560719603606277097/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1660
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1661
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (4836562540104694306723868371868988333827/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4836562540104694306723868371868988333827/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (19358308376247492626998915644382262157889/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19358308376247492626998915644382262157889/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (38704558536666269853894389131858215493197/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38704558536666269853894389131858215493197/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1661 BracketBatch0103.bracket1662 (38704558536666269853894389131858215493197/20000000000000000000000000000000000000000) (383861721025480281588501106865515447919/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1661 BracketBatch0103.bracket1662
  (38704558536666269853894389131858215493197/20000000000000000000000000000000000000000) (383861721025480281588501106865515447919/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1661
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1662
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (9679154188123746313499457822191131078943/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9679154188123746313499457822191131078943/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (9685191931417694798429252311035195010393/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9685191931417694798429252311035195010393/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2420543264942680138991088766653290761167/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2420543264942680138991088766653290761167/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1662 BracketBatch0103.bracket1663 (2420543264942680138991088766653290761167/1250000000000000000000000000000000000000) (96043846064447554113887817172831580989/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1662 BracketBatch0103.bracket1663
  (2420543264942680138991088766653290761167/1250000000000000000000000000000000000000) (96043846064447554113887817172831580989/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1662
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1663
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (19370383862835389596858504622070390020783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19370383862835389596858504622070390020783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1211404791168325505052407376257059597071/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1211404791168325505052407376257059597071/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (38752860521528597677697022642183343573919/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38752860521528597677697022642183343573919/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0207.rows ScalarLogs0207.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1663 BracketBatch0104.bracket1664 (38752860521528597677697022642183343573919/20000000000000000000000000000000000000000) (15379575941652321157759578956285058291/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1663 BracketBatch0104.bracket1664
  (38752860521528597677697022642183343573919/20000000000000000000000000000000000000000) (15379575941652321157759578956285058291/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1663
