module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0295
public import BecknerOnofri.EntropyScalarCertificate.Bessel0296
public import BecknerOnofri.EntropyScalarCertificate.Bessel0636
public import BecknerOnofri.EntropyScalarCertificate.Bessel0637
public import BecknerOnofri.EntropyScalarCertificate.Brackets0118
public import BecknerOnofri.EntropyScalarCertificate.Logs0236
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1888
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (27818787711916393337768549973654543065297/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27818787711916393337768549973654543065297/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (27956023783691718030819799593201790019201/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27956023783691718030819799593201790019201/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (27887405747804055684294174783428166542249/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27887405747804055684294174783428166542249/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1888 BracketBatch0118.bracket1889 (27887405747804055684294174783428166542249/10000000000000000000000000000000000000000) (1157053093335374028992773376969901137271/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1888 BracketBatch0118.bracket1889
  (27887405747804055684294174783428166542249/10000000000000000000000000000000000000000) (1157053093335374028992773376969901137271/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1888
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1889
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (13978011891845859015409899796600895009599/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13978011891845859015409899796600895009599/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (2809474953863385455081840428766287308367/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2809474953863385455081840428766287308367/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (14012693330581393145409550970216165775717/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14012693330581393145409550970216165775717/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1889 BracketBatch0118.bracket1890 (14012693330581393145409550970216165775717/5000000000000000000000000000000000000000) (1162666045029224476246229422998997653921/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1889 BracketBatch0118.bracket1890
  (14012693330581393145409550970216165775717/5000000000000000000000000000000000000000) (1162666045029224476246229422998997653921/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1889
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1890
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (28094749538633854550818404287662873083667/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28094749538633854550818404287662873083667/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (14117494422680179781732320812572719398833/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14117494422680179781732320812572719398833/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (56329738383994214114283045912808311881333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (56329738383994214114283045912808311881333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1890 BracketBatch0118.bracket1891 (56329738383994214114283045912808311881333/20000000000000000000000000000000000000000) (584159256323837879946457859849747847783/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1890 BracketBatch0118.bracket1891
  (56329738383994214114283045912808311881333/20000000000000000000000000000000000000000) (584159256323837879946457859849747847783/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1890
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1891
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (28234988845360359563464641625145438797663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28234988845360359563464641625145438797663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (5675353215837674646671736709462763117503/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5675353215837674646671736709462763117503/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (28305877462274366398411662586229627192589/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28305877462274366398411662586229627192589/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1891 BracketBatch0118.bracket1892 (28305877462274366398411662586229627192589/10000000000000000000000000000000000000000) (1174010885517601563592754897801064571259/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1891 BracketBatch0118.bracket1892
  (28305877462274366398411662586229627192589/10000000000000000000000000000000000000000) (1174010885517601563592754897801064571259/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1891
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1892
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3547095759898546654169835443414226948439/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3547095759898546654169835443414226948439/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (14260053067945303300925985809060811424611/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14260053067945303300925985809060811424611/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (28448436107539489917605327582717719218367/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28448436107539489917605327582717719218367/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1892 BracketBatch0118.bracket1893 (28448436107539489917605327582717719218367/10000000000000000000000000000000000000000) (147467944808982801988947360435946536727/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1892 BracketBatch0118.bracket1893
  (28448436107539489917605327582717719218367/10000000000000000000000000000000000000000) (147467944808982801988947360435946536727/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1892
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1893
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (28520106135890606601851971618121622849219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28520106135890606601851971618121622849219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (5733006889181120175727552111956653425721/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5733006889181120175727552111956653425721/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1787035643181131483765304130559527811807/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1787035643181131483765304130559527811807/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1893 BracketBatch0118.bracket1894 (1787035643181131483765304130559527811807/625000000000000000000000000000000000000) (592758465986473001872928747101898770857/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1893 BracketBatch0118.bracket1894
  (1787035643181131483765304130559527811807/625000000000000000000000000000000000000) (592758465986473001872928747101898770857/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1893
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1894
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (14332517222952800439318880279891633564301/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14332517222952800439318880279891633564301/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (7202894247254907258903701295229632865929/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7202894247254907258903701295229632865929/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (28738305717462614957126282870350899296159/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28738305717462614957126282870350899296159/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1894 BracketBatch0118.bracket1895 (28738305717462614957126282870350899296159/10000000000000000000000000000000000000000) (1191331412240186643072077506991219480599/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1894 BracketBatch0118.bracket1895
  (28738305717462614957126282870350899296159/10000000000000000000000000000000000000000) (1191331412240186643072077506991219480599/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1894
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1895
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (28811576989019629035614805180918531463713/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28811576989019629035614805180918531463713/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (7239940077384590919542446437895125257987/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7239940077384590919542446437895125257987/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (57771337298557992713784590932499032495661/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57771337298557992713784590932499032495661/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0236.rows ScalarLogs0236.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1895 BracketBatch0118.bracket1896 (57771337298557992713784590932499032495661/20000000000000000000000000000000000000000) (1197187411380667572683546676750369810063/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1895 BracketBatch0118.bracket1896
  (57771337298557992713784590932499032495661/20000000000000000000000000000000000000000) (1197187411380667572683546676750369810063/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1895
