module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0182
public import BecknerOnofri.EntropyScalarCertificate.Bessel0183
public import BecknerOnofri.EntropyScalarCertificate.Bessel0580
public import BecknerOnofri.EntropyScalarCertificate.Brackets0073
public import BecknerOnofri.EntropyScalarCertificate.Logs0146
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1168
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4348614282179212345068327108149944104133/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4348614282179212345068327108149944104133/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (8721809828211449339991089596688475954853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8721809828211449339991089596688475954853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (17419038392569874030127743812988364163119/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17419038392569874030127743812988364163119/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1168 BracketBatch0073.bracket1169 (17419038392569874030127743812988364163119/20000000000000000000000000000000000000000) (173070672581910795998857267251242371347/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1168 BracketBatch0073.bracket1169
  (17419038392569874030127743812988364163119/20000000000000000000000000000000000000000) (173070672581910795998857267251242371347/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1168
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1169
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (174436196564228986799821791933769519097/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (174436196564228986799821791933769519097/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (874649075019328025775853290977502755391/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (874649075019328025775853290977502755391/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (436707514460118239943740562661587587719/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (436707514460118239943740562661587587719/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1169 BracketBatch0073.bracket1170 (436707514460118239943740562661587587719/500000000000000000000000000000000000000) (174299739665417486478932143639029691639/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1169 BracketBatch0073.bracket1170
  (436707514460118239943740562661587587719/500000000000000000000000000000000000000) (174299739665417486478932143639029691639/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1169
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1170
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (8746490750193280257758532909775027553907/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8746490750193280257758532909775027553907/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (4385636098283462209302097100669509593121/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4385636098283462209302097100669509593121/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (17517762946760204676362727111114046740149/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17517762946760204676362727111114046740149/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1170 BracketBatch0073.bracket1171 (17517762946760204676362727111114046740149/20000000000000000000000000000000000000000) (175536577206877511697046382308120714353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1170 BracketBatch0073.bracket1171
  (17517762946760204676362727111114046740149/20000000000000000000000000000000000000000) (175536577206877511697046382308120714353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1170
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1171
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (8771272196566924418604194201339019186239/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8771272196566924418604194201339019186239/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (6871996128117113528232147338758516917/7812500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6871996128117113528232147338758516917/7812500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (17567427240556829734741342794949920839999/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17567427240556829734741342794949920839999/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1171 BracketBatch0073.bracket1172 (17567427240556829734741342794949920839999/20000000000000000000000000000000000000000) (44195309200098348892257859911303464197/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1171 BracketBatch0073.bracket1172
  (17567427240556829734741342794949920839999/20000000000000000000000000000000000000000) (44195309200098348892257859911303464197/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1171
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1172
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (8796155043989905316137148593610901653757/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8796155043989905316137148593610901653757/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (4410570089837115844252663383836334618747/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4410570089837115844252663383836334618747/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (17617295223664137004642475361283570891251/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17617295223664137004642475361283570891251/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1172 BracketBatch0073.bracket1173 (17617295223664137004642475361283570891251/20000000000000000000000000000000000000000) (35606754103700498232763482044172500193/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1172 BracketBatch0073.bracket1173
  (17617295223664137004642475361283570891251/20000000000000000000000000000000000000000) (35606754103700498232763482044172500193/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1172
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1173
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (8821140179674231688505326767672669237491/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8821140179674231688505326767672669237491/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2211557125387333530652130837942447274049/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2211557125387333530652130837942447274049/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (17667368681223565811113850119442458333687/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17667368681223565811113850119442458333687/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1173 BracketBatch0073.bracket1174 (17667368681223565811113850119442458333687/20000000000000000000000000000000000000000) (22411778864841044608523255425709279557/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1173 BracketBatch0073.bracket1174
  (17667368681223565811113850119442458333687/20000000000000000000000000000000000000000) (22411778864841044608523255425709279557/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1173
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1174
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (8846228501549334122608523351769789096193/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8846228501549334122608523351769789096193/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (8871420918428033587891364312028692432471/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8871420918428033587891364312028692432471/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (2214706177497170963812485957974810191083/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2214706177497170963812485957974810191083/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1174 BracketBatch0073.bracket1175 (2214706177497170963812485957974810191083/2500000000000000000000000000000000000000) (5642583470320145799352827280351172861/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1174 BracketBatch0073.bracket1175
  (2214706177497170963812485957974810191083/2500000000000000000000000000000000000000) (5642583470320145799352827280351172861/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1174
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1175
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (2217855229607008396972841078007173108117/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2217855229607008396972841078007173108117/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (8896718350175607518121903581551028160211/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8896718350175607518121903581551028160211/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (17768139268603641106013267893579720592679/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17768139268603641106013267893579720592679/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0146.rows ScalarLogs0146.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0073.bracket1175 BracketBatch0073.bracket1176 (17768139268603641106013267893579720592679/20000000000000000000000000000000000000000) (45459786115163462718590251980355586033/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0073.bracket1175 BracketBatch0073.bracket1176
  (17768139268603641106013267893579720592679/20000000000000000000000000000000000000000) (45459786115163462718590251980355586033/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1175
