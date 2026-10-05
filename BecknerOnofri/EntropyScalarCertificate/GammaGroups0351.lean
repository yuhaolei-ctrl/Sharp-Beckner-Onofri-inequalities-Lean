import BecknerOnofri.EntropyScalarCertificate.Bessel0438
import BecknerOnofri.EntropyScalarCertificate.Bessel0439
import BecknerOnofri.EntropyScalarCertificate.Bessel0440
import BecknerOnofri.EntropyScalarCertificate.Bessel0708
import BecknerOnofri.EntropyScalarCertificate.Brackets0175
import BecknerOnofri.EntropyScalarCertificate.Brackets0176
import BecknerOnofri.EntropyScalarCertificate.Logs0351
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2808
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (481396684267383881031819850528767949346137/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (481396684267383881031819850528767949346137/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (482323017149651984095148238678984837537691/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (482323017149651984095148238678984837537691/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (240929925354258966281742022301938196720957/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (240929925354258966281742022301938196720957/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2808 BracketBatch0175.bracket2809 (240929925354258966281742022301938196720957/2500000000000000000000000000000000000000) (3027572690486931118507751920115456867113/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2808 BracketBatch0175.bracket2809
  (240929925354258966281742022301938196720957/2500000000000000000000000000000000000000) (3027572690486931118507751920115456867113/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2808
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2809
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (964646034299303968190296477357969675075379/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (964646034299303968190296477357969675075379/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (483252926625212707837182665714035318257361/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (483252926625212707837182665714035318257361/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1931151887549729383864661808786040311590101/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1931151887549729383864661808786040311590101/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2809 BracketBatch0175.bracket2810 (1931151887549729383864661808786040311590101/20000000000000000000000000000000000000000) (6058102823888920246113625520552202484857/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2809 BracketBatch0175.bracket2810
  (1931151887549729383864661808786040311590101/20000000000000000000000000000000000000000) (6058102823888920246113625520552202484857/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2809
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2810
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (966505853250425415674365331428070636514719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (966505853250425415674365331428070636514719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (193674573379196643235943009104119488727451/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (193674573379196643235943009104119488727451/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (967439360073204315927040188474334040075987/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (967439360073204315927040188474334040075987/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2810 BracketBatch0175.bracket2811 (967439360073204315927040188474334040075987/10000000000000000000000000000000000000000) (6061066060771890722386348781647773523809/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2810 BracketBatch0175.bracket2811
  (967439360073204315927040188474334040075987/10000000000000000000000000000000000000000) (6061066060771890722386348781647773523809/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2810
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2811
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (242093216723995804044928761380149360909313/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (242093216723995804044928761380149360909313/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (242561779266398692291281750108215895590607/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (242561779266398692291281750108215895590607/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (6058187449879931204202631393604565706249/62500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6058187449879931204202631393604565706249/62500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2811 BracketBatch0175.bracket2812 (6058187449879931204202631393604565706249/62500000000000000000000000000000000000) (6064035113266235697852102016211696322249/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2811 BracketBatch0175.bracket2812
  (6058187449879931204202631393604565706249/62500000000000000000000000000000000000) (6064035113266235697852102016211696322249/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2811
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2812
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (38809884682623790766605080017314543294497/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38809884682623790766605080017314543294497/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (12151608073922096330324745455710379467451/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12151608073922096330324745455710379467451/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (388475152595872495118221327377938787951701/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (388475152595872495118221327377938787951701/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2812 BracketBatch0175.bracket2813 (388475152595872495118221327377938787951701/4000000000000000000000000000000000000000) (6067010003133283700331185644166970734189/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2812 BracketBatch0175.bracket2813
  (388475152595872495118221327377938787951701/4000000000000000000000000000000000000000) (6067010003133283700331185644166970734189/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2812
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2813
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (972128645913767706425979636456830357396077/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (972128645913767706425979636456830357396077/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (974017495923060302914629622708064623585367/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (974017495923060302914629622708064623585367/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (486536535459207002335152314791223745245361/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (486536535459207002335152314791223745245361/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2813 BracketBatch0175.bracket2814 (486536535459207002335152314791223745245361/5000000000000000000000000000000000000000) (6069990752253053102566263949440364148299/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2813 BracketBatch0175.bracket2814
  (486536535459207002335152314791223745245361/5000000000000000000000000000000000000000) (6069990752253053102566263949440364148299/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2813
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2814
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (243504373980765075728657405677016155896341/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (243504373980765075728657405677016155896341/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (243978427476819712857509313317698344651671/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (243978427476819712857509313317698344651671/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (121870700364396197146541679748678625137003/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (121870700364396197146541679748678625137003/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2814 BracketBatch0175.bracket2815 (121870700364396197146541679748678625137003/1250000000000000000000000000000000000000) (6072977382625082245115690962709476804383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2814 BracketBatch0175.bracket2815
  (121870700364396197146541679748678625137003/1250000000000000000000000000000000000000) (6072977382625082245115690962709476804383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2814
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2815
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (975913709907278851430037253270793378606681/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (975913709907278851430037253270793378606681/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (61113583188419531658877243348241833104383/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61113583188419531658877243348241833104383/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1953731040921991357972073146842662708276809/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1953731040921991357972073146842662708276809/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0351.rows ScalarLogs0351.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2815 BracketBatch0176.bracket2816 (1953731040921991357972073146842662708276809/20000000000000000000000000000000000000000) (6075969916369266393256859980429199993931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2815 BracketBatch0176.bracket2816
  (1953731040921991357972073146842662708276809/20000000000000000000000000000000000000000) (6075969916369266393256859980429199993931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2815
