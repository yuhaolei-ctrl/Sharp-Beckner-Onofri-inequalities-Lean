module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0148
public import BecknerOnofri.EntropyScalarCertificate.Bessel0149
public import BecknerOnofri.EntropyScalarCertificate.Bessel0150
public import BecknerOnofri.EntropyScalarCertificate.Bessel0563
public import BecknerOnofri.EntropyScalarCertificate.Brackets0059
public import BecknerOnofri.EntropyScalarCertificate.Brackets0060
public import BecknerOnofri.EntropyScalarCertificate.Logs0119
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0952
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4827063209542521834877357319281534508417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4827063209542521834877357319281534508417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (2420441765404284373639194845109219763707/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2420441765404284373639194845109219763707/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (9667946740351090582155747009499974035831/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9667946740351090582155747009499974035831/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0952 BracketBatch0059.bracket0953 (9667946740351090582155747009499974035831/20000000000000000000000000000000000000000) (14995711916759760071417738071532781869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0952 BracketBatch0059.bracket0953
  (9667946740351090582155747009499974035831/20000000000000000000000000000000000000000) (14995711916759760071417738071532781869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0952
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0953
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (4840883530808568747278389690218439527411/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4840883530808568747278389690218439527411/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (4854727540988249987448459272826991018787/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4854727540988249987448459272826991018787/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (4847805535898409367363424481522715273099/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4847805535898409367363424481522715273099/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0953 BracketBatch0059.bracket0954 (4847805535898409367363424481522715273099/10000000000000000000000000000000000000000) (6056353864995577165267691354872619329/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0953 BracketBatch0059.bracket0954
  (4847805535898409367363424481522715273099/10000000000000000000000000000000000000000) (6056353864995577165267691354872619329/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0953
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0954
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (151710235655882812107764352275843469337/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (151710235655882812107764352275843469337/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (4868595368914580079378378661406211189401/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4868595368914580079378378661406211189401/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (1944664581980566013365367586846640441637/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1944664581980566013365367586846640441637/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0954 BracketBatch0059.bracket0955 (1944664581980566013365367586846640441637/4000000000000000000000000000000000000000) (30574322590166104488182649556566944663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0954 BracketBatch0059.bracket0955
  (1944664581980566013365367586846640441637/4000000000000000000000000000000000000000) (30574322590166104488182649556566944663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0954
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0955
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2434297684457290039689189330703105594699/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2434297684457290039689189330703105594699/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4882487144266537318219407496449460116289/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4882487144266537318219407496449460116289/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (9751082513181117397597786157855671305687/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9751082513181117397597786157855671305687/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0955 BracketBatch0059.bracket0956 (9751082513181117397597786157855671305687/20000000000000000000000000000000000000000) (30869096506933256636764488373027964401/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0955 BracketBatch0059.bracket0956
  (9751082513181117397597786157855671305687/20000000000000000000000000000000000000000) (30869096506933256636764488373027964401/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0955
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0956
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2441243572133268659109703748224730058143/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2441243572133268659109703748224730058143/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4896402997576759114656596315389207526617/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4896402997576759114656596315389207526617/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (9778890141843296432876003811838667642903/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9778890141843296432876003811838667642903/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0956 BracketBatch0059.bracket0957 (9778890141843296432876003811838667642903/20000000000000000000000000000000000000000) (6233220803254097604401997117065838683/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0956 BracketBatch0059.bracket0957
  (9778890141843296432876003811838667642903/20000000000000000000000000000000000000000) (6233220803254097604401997117065838683/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0956
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0957
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2448201498788379557328298157694603763307/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2448201498788379557328298157694603763307/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (4910343060239321416298875448141838113269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4910343060239321416298875448141838113269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (9806746057816080530955471763531045639883/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9806746057816080530955471763531045639883/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0957 BracketBatch0059.bracket0958 (9806746057816080530955471763531045639883/20000000000000000000000000000000000000000) (3146535812270606558977645987138371473/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0957 BracketBatch0059.bracket0958
  (9806746057816080530955471763531045639883/20000000000000000000000000000000000000000) (3146535812270606558977645987138371473/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0957
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0958
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2455171530119660708149437724070919056633/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2455171530119660708149437724070919056633/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (196972298580704132001638367843019393307/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (196972298580704132001638367843019393307/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (9834650524756924716339834644217322945941/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9834650524756924716339834644217322945941/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0958 BracketBatch0059.bracket0959 (9834650524756924716339834644217322945941/20000000000000000000000000000000000000000) (15883435947352190386664585152335867997/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0958 BracketBatch0059.bracket0959
  (9834650524756924716339834644217322945941/20000000000000000000000000000000000000000) (15883435947352190386664585152335867997/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0958
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0959
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (153884608266175103126279974877358901021/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (153884608266175103126279974877358901021/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (617287042944029730712052308625335178477/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (617287042944029730712052308625335178477/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1232825476008730143217172208134770782561/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1232825476008730143217172208134770782561/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0119.rows ScalarLogs0119.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0959 BracketBatch0060.bracket0960 (1232825476008730143217172208134770782561/2500000000000000000000000000000000000000) (32070658465068949624948620851300599481/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0959 BracketBatch0060.bracket0960
  (1232825476008730143217172208134770782561/2500000000000000000000000000000000000000) (32070658465068949624948620851300599481/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0959
