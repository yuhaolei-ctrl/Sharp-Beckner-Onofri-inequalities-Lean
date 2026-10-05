module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0130
public import BecknerOnofri.EntropyScalarCertificate.Bessel0131
public import BecknerOnofri.EntropyScalarCertificate.Bessel0553
public import BecknerOnofri.EntropyScalarCertificate.Bessel0554
public import BecknerOnofri.EntropyScalarCertificate.Brackets0052
public import BecknerOnofri.EntropyScalarCertificate.Logs0104
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0832
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1654418388039497299264514453361267278091/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1654418388039497299264514453361267278091/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1660277484812843001978906673331303274309/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1660277484812843001978906673331303274309/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (8286739682130850753108552816731426381/25000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8286739682130850753108552816731426381/25000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0832 BracketBatch0052.bracket0833 (8286739682130850753108552816731426381/25000000000000000000000000000000000000) (3937170886476417297820083015832477579/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0832 BracketBatch0052.bracket0833
  (8286739682130850753108552816731426381/25000000000000000000000000000000000000) (3937170886476417297820083015832477579/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0832
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0833
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (664110993925137200791562669332521309723/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (664110993925137200791562669332521309723/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (3332285837573691532158351645431415283303/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3332285837573691532158351645431415283303/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (3326420403599688768058082496047010915959/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3326420403599688768058082496047010915959/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0833 BracketBatch0052.bracket0834 (3326420403599688768058082496047010915959/10000000000000000000000000000000000000000) (1994370482664490862438791683522518849/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0833 BracketBatch0052.bracket0834
  (3326420403599688768058082496047010915959/10000000000000000000000000000000000000000) (1994370482664490862438791683522518849/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0833
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0834
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (33322858375736915321583516454314152833/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33322858375736915321583516454314152833/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (3344029445503056813719035979735332363033/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3344029445503056813719035979735332363033/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (6676315283076748345877387625166747646333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6676315283076748345877387625166747646333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0834 BracketBatch0052.bracket0835 (6676315283076748345877387625166747646333/20000000000000000000000000000000000000000) (8081653786431968932176986261547947923/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0834 BracketBatch0052.bracket0835
  (6676315283076748345877387625166747646333/20000000000000000000000000000000000000000) (8081653786431968932176986261547947923/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0834
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0835
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (334402944550305681371903597973533236303/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (334402944550305681371903597973533236303/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (335578585930767521357515893534027760081/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (335578585930767521357515893534027760081/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (20936922827533537585294359109611281137/62500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20936922827533537585294359109611281137/62500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0835 BracketBatch0052.bracket0836 (20936922827533537585294359109611281137/62500000000000000000000000000000000000) (4093432336773830217294223007042441077/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0835 BracketBatch0052.bracket0836
  (20936922827533537585294359109611281137/62500000000000000000000000000000000000) (4093432336773830217294223007042441077/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0835
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0836
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3355785859307675213575158935340277600807/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3355785859307675213575158935340277600807/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (33675551451977053163040632837635939457/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33675551451977053163040632837635939457/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (6723341004505380529879222219103871546507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6723341004505380529879222219103871546507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0836 BracketBatch0052.bracket0837 (6723341004505380529879222219103871546507/20000000000000000000000000000000000000000) (8293121959802347173401612234446201117/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0836 BracketBatch0052.bracket0837
  (6723341004505380529879222219103871546507/20000000000000000000000000000000000000000) (8293121959802347173401612234446201117/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0836
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0837
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (3367555145197705316304063283763593945697/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3367555145197705316304063283763593945697/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (211208585606375572044741245315520645069/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (211208585606375572044741245315520645069/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (6746892514899714469019923208811924266801/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6746892514899714469019923208811924266801/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0837 BracketBatch0052.bracket0838 (6746892514899714469019923208811924266801/20000000000000000000000000000000000000000) (2100108261914300737430422954301571401/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0837 BracketBatch0052.bracket0838
  (6746892514899714469019923208811924266801/20000000000000000000000000000000000000000) (2100108261914300737430422954301571401/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0837
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0838
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3379337369702009152715859925048330321101/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3379337369702009152715859925048330321101/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (3391132599670611389161183014390652984917/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3391132599670611389161183014390652984917/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (3385234984686310270938521469719491653009/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3385234984686310270938521469719491653009/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0838 BracketBatch0052.bracket0839 (3385234984686310270938521469719491653009/10000000000000000000000000000000000000000) (8508805374377717650867539482459190623/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0838 BracketBatch0052.bracket0839
  (3385234984686310270938521469719491653009/10000000000000000000000000000000000000000) (8508805374377717650867539482459190623/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0838
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0839
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1695566299835305694580591507195326492457/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1695566299835305694580591507195326492457/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (340294090227717970364417917179334950923/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (340294090227717970364417917179334950923/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (106157398467934235825083784159125038971/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (106157398467934235825083784159125038971/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0104.rows ScalarLogs0104.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0839 BracketBatch0052.bracket0840 (106157398467934235825083784159125038971/312500000000000000000000000000000000000) (4309123206087622755902646446057620907/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0839 BracketBatch0052.bracket0840
  (106157398467934235825083784159125038971/312500000000000000000000000000000000000) (4309123206087622755902646446057620907/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0839
