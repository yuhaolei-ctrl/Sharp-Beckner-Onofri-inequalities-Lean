module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0475
public import BecknerOnofri.EntropyScalarCertificate.Bessel0476
public import BecknerOnofri.EntropyScalarCertificate.Bessel0726
public import BecknerOnofri.EntropyScalarCertificate.Bessel0727
public import BecknerOnofri.EntropyScalarCertificate.Brackets0190
public import BecknerOnofri.EntropyScalarCertificate.Logs0380
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3040
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (347472764176654074393618118857508279454283/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (347472764176654074393618118857508279454283/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (871706489537439159962078725594111359190907/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (871706489537439159962078725594111359190907/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (3480776799958148691892248045475764115653229/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3480776799958148691892248045475764115653229/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3040 BracketBatch0190.bracket3041 (3480776799958148691892248045475764115653229/20000000000000000000000000000000000000000) (6961070956315403149516490018770841225857/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3040 BracketBatch0190.bracket3041
  (3480776799958148691892248045475764115653229/20000000000000000000000000000000000000000) (6961070956315403149516490018770841225857/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3040
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3041
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1743412979074878319924157451188222718381811/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1743412979074878319924157451188222718381811/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (874752219569147297003423212131296857894949/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (874752219569147297003423212131296857894949/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (3492917418213172913931003875450816434171709/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3492917418213172913931003875450816434171709/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3041 BracketBatch0190.bracket3042 (3492917418213172913931003875450816434171709/20000000000000000000000000000000000000000) (6966341047589189684440352066987048841127/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3041 BracketBatch0190.bracket3042
  (3492917418213172913931003875450816434171709/20000000000000000000000000000000000000000) (6966341047589189684440352066987048841127/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3041
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3042
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (349900887827658918801369284852518743157979/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (349900887827658918801369284852518743157979/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (351127729271275562828086845372723872037017/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (351127729271275562828086845372723872037017/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (175257154274733620407364032556310653798749/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (175257154274733620407364032556310653798749/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3042 BracketBatch0190.bracket3043 (175257154274733620407364032556310653798749/1000000000000000000000000000000000000000) (871453490292283148259086638802588256977/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3042 BracketBatch0190.bracket3043
  (175257154274733620407364032556310653798749/1000000000000000000000000000000000000000) (871453490292283148259086638802588256977/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3042
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3043
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (877819323178188907070217113431809680092541/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (877819323178188907070217113431809680092541/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1761816052283576158466143128348018336555711/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1761816052283576158466143128348018336555711/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (3517454698639953972606577355211637696740793/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3517454698639953972606577355211637696740793/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3043 BracketBatch0190.bracket3044 (3517454698639953972606577355211637696740793/20000000000000000000000000000000000000000) (1395386334130972688590634532628209642043/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3043 BracketBatch0190.bracket3044
  (3517454698639953972606577355211637696740793/20000000000000000000000000000000000000000) (1395386334130972688590634532628209642043/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3043
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3044
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (440454013070894039616535782087004584138927/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (440454013070894039616535782087004584138927/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (884018557428366416284282427760582495364043/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (884018557428366416284282427760582495364043/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1764926583570154495517353991934591663641897/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1764926583570154495517353991934591663641897/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3044 BracketBatch0190.bracket3045 (1764926583570154495517353991934591663641897/10000000000000000000000000000000000000000) (55858019064817384224453968511480080801/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3044 BracketBatch0190.bracket3045
  (1764926583570154495517353991934591663641897/10000000000000000000000000000000000000000) (55858019064817384224453968511480080801/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3044
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3045
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1768037114856732832568564855521164990728083/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1768037114856732832568564855521164990728083/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1774302298508249101877114794334461985447661/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1774302298508249101877114794334461985447661/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (27674526666913921362856872264497085751373/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27674526666913921362856872264497085751373/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3045 BracketBatch0190.bracket3046 (27674526666913921362856872264497085751373/156250000000000000000000000000000000000) (6987590150710951301188992449673653184237/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3045 BracketBatch0190.bracket3046
  (27674526666913921362856872264497085751373/156250000000000000000000000000000000000) (6987590150710951301188992449673653184237/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3045
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3046
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (887151149254124550938557397167230992723829/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (887151149254124550938557397167230992723829/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1780612074281663616574278812480885221610929/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1780612074281663616574278812480885221610929/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (3554914372789912718451393606815347207058587/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3554914372789912718451393606815347207058587/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3046 BracketBatch0190.bracket3047 (3554914372789912718451393606815347207058587/20000000000000000000000000000000000000000) (11188712103961330935440951302976368849/16000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3046 BracketBatch0190.bracket3047
  (3554914372789912718451393606815347207058587/20000000000000000000000000000000000000000) (11188712103961330935440951302976368849/16000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3046
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3047
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (890306037140831808287139406240442610805463/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (890306037140831808287139406240442610805463/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (893483459974854218161661259204997222840503/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (893483459974854218161661259204997222840503/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (891894748557843013224400332722719916822983/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (891894748557843013224400332722719916822983/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0380.rows ScalarLogs0380.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3047 BracketBatch0190.bracket3048 (891894748557843013224400332722719916822983/5000000000000000000000000000000000000000) (1399663443570262350416656235963728687519/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3047 BracketBatch0190.bracket3048
  (891894748557843013224400332722719916822983/5000000000000000000000000000000000000000) (1399663443570262350416656235963728687519/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3047
