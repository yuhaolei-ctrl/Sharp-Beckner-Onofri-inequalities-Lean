module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0145
public import BecknerOnofri.EntropyScalarCertificate.Bessel0146
public import BecknerOnofri.EntropyScalarCertificate.Bessel0561
public import BecknerOnofri.EntropyScalarCertificate.Bessel0562
public import BecknerOnofri.EntropyScalarCertificate.Brackets0058
public import BecknerOnofri.EntropyScalarCertificate.Logs0116
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0928
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (4502161335608504876571574985642898645611/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4502161335608504876571574985642898645611/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (4515449700624503146332147847614431222881/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4515449700624503146332147847614431222881/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2254402759058252005725930708314332467123/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2254402759058252005725930708314332467123/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0928 BracketBatch0058.bracket0929 (2254402759058252005725930708314332467123/5000000000000000000000000000000000000000) (11826235537510115674463321193799441591/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0928 BracketBatch0058.bracket0929
  (2254402759058252005725930708314332467123/5000000000000000000000000000000000000000) (11826235537510115674463321193799441591/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0928
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0929
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2257724850312251573166073923807215611439/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2257724850312251573166073923807215611439/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (905751779543660167523956801881749073019/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (905751779543660167523956801881749073019/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (9044208598342803983951931857023176587973/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9044208598342803983951931857023176587973/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0929 BracketBatch0058.bracket0930 (9044208598342803983951931857023176587973/20000000000000000000000000000000000000000) (11946783605377984714619638853574377909/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0929 BracketBatch0058.bracket0930
  (9044208598342803983951931857023176587973/20000000000000000000000000000000000000000) (11946783605377984714619638853574377909/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0929
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0930
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1132189724429575209404946002352186341273/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1132189724429575209404946002352186341273/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (4542089037527498993557093322071527315759/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4542089037527498993557093322071527315759/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (9070847935245799831176877331480272680851/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9070847935245799831176877331480272680851/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0930 BracketBatch0058.bracket0931 (9070847935245799831176877331480272680851/20000000000000000000000000000000000000000) (24136580741396727246456391332450310057/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0930 BracketBatch0058.bracket0931
  (9070847935245799831176877331480272680851/20000000000000000000000000000000000000000) (24136580741396727246456391332450310057/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0930
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0931
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1135522259381874748389273330517881828939/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1135522259381874748389273330517881828939/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (4555440231373614958341670559057014707049/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4555440231373614958341670559057014707049/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1819505853780222790379752776225708404561/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1819505853780222790379752776225708404561/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0931 BracketBatch0058.bracket0932 (1819505853780222790379752776225708404561/4000000000000000000000000000000000000000) (12190761573967255905212956233133058207/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0931 BracketBatch0058.bracket0932
  (1819505853780222790379752776225708404561/4000000000000000000000000000000000000000) (12190761573967255905212956233133058207/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0931
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0932
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (2277720115686807479170835279528507353523/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2277720115686807479170835279528507353523/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (913762518253609989262005149610158905201/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (913762518253609989262005149610158905201/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (9124252822641664904651696307107809233051/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9124252822641664904651696307107809233051/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0932 BracketBatch0058.bracket0933 (9124252822641664904651696307107809233051/20000000000000000000000000000000000000000) (24628405966185435835661301305446512199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0932 BracketBatch0058.bracket0933
  (9124252822641664904651696307107809233051/20000000000000000000000000000000000000000) (24628405966185435835661301305446512199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0932
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0933
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2284406295634024973155012874025397263001/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2284406295634024973155012874025397263001/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2291103114959059350065944882745872993821/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2291103114959059350065944882745872993821/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (2287754705296542161610478878385635128411/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2287754705296542161610478878385635128411/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0933 BracketBatch0058.bracket0934 (2287754705296542161610478878385635128411/5000000000000000000000000000000000000000) (2487724078710398509050669002115028197/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0933 BracketBatch0058.bracket0934
  (2287754705296542161610478878385635128411/5000000000000000000000000000000000000000) (2487724078710398509050669002115028197/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0933
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0934
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (4582206229918118700131889765491745987639/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4582206229918118700131889765491745987639/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (2297810630366571005415538409565188209633/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2297810630366571005415538409565188209633/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1835565498130252142192593316924424481381/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1835565498130252142192593316924424481381/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0934 BracketBatch0058.bracket0935 (1835565498130252142192593316924424481381/4000000000000000000000000000000000000000) (2512803925710024466940276243799711943/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0934 BracketBatch0058.bracket0935
  (1835565498130252142192593316924424481381/4000000000000000000000000000000000000000) (2512803925710024466940276243799711943/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0934
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0935
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4595621260733142010831076819130376419263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4595621260733142010831076819130376419263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (4609057797830602883362362940153615367941/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4609057797830602883362362940153615367941/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2301169764640936223548359939820997946801/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2301169764640936223548359939820997946801/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0116.rows ScalarLogs0116.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0058.bracket0935 BracketBatch0058.bracket0936 (2301169764640936223548359939820997946801/5000000000000000000000000000000000000000) (12690406539180059591510831718419707811/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0058.bracket0935 BracketBatch0058.bracket0936
  (2301169764640936223548359939820997946801/5000000000000000000000000000000000000000) (12690406539180059591510831718419707811/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0935
