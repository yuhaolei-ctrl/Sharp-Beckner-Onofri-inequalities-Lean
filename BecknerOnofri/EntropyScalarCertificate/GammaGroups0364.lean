module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0455
public import BecknerOnofri.EntropyScalarCertificate.Bessel0456
public import BecknerOnofri.EntropyScalarCertificate.Bessel0716
public import BecknerOnofri.EntropyScalarCertificate.Bessel0717
public import BecknerOnofri.EntropyScalarCertificate.Brackets0182
public import BecknerOnofri.EntropyScalarCertificate.Logs0364
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2912
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (24063539947215473459148883133082939460873/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24063539947215473459148883133082939460873/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1206073188072609247161852621411544173193517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1206073188072609247161852621411544173193517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2409250185433382920119296778065691146237167/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2409250185433382920119296778065691146237167/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2912 BracketBatch0182.bracket2913 (2409250185433382920119296778065691146237167/20000000000000000000000000000000000000000) (1279664226825006132791356066057996199887/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2912 BracketBatch0182.bracket2913
  (2409250185433382920119296778065691146237167/20000000000000000000000000000000000000000) (1279664226825006132791356066057996199887/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2912
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2913
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (603036594036304623580926310705772086596757/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (603036594036304623580926310705772086596757/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1208983370089927977115494546621366470819239/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1208983370089927977115494546621366470819239/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2415056558162537224277347168032910644012753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2415056558162537224277347168032910644012753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2913 BracketBatch0182.bracket2914 (2415056558162537224277347168032910644012753/20000000000000000000000000000000000000000) (3201011493105819252979950048807645056377/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2913 BracketBatch0182.bracket2914
  (2415056558162537224277347168032910644012753/20000000000000000000000000000000000000000) (3201011493105819252979950048807645056377/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2913
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2914
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (302245842522481994278873636655341617704809/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (302245842522481994278873636655341617704809/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1211907645044487064294919879459915151684461/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1211907645044487064294919879459915151684461/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (2420891015134415041410414426081281622503697/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2420891015134415041410414426081281622503697/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2914 BracketBatch0182.bracket2915 (2420891015134415041410414426081281622503697/20000000000000000000000000000000000000000) (6405733700986467029899799155427613076651/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2914 BracketBatch0182.bracket2915
  (2420891015134415041410414426081281622503697/20000000000000000000000000000000000000000) (6405733700986467029899799155427613076651/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2914
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2915
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (605953822522243532147459939729957575842229/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (605953822522243532147459939729957575842229/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (607423057777379899822195984763876710032851/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (607423057777379899822195984763876710032851/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (30334422007490585799241398112345857146877/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30334422007490585799241398112345857146877/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2915 BracketBatch0182.bracket2916 (30334422007490585799241398112345857146877/250000000000000000000000000000000000000) (6409453318301797703531809361158885856193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2915 BracketBatch0182.bracket2916
  (30334422007490585799241398112345857146877/250000000000000000000000000000000000000) (6409453318301797703531809361158885856193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2915
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2916
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1214846115554759799644391969527753420065699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1214846115554759799644391969527753420065699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (19028107581842803264789440001914946376849/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19028107581842803264789440001914946376849/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (486529000158539841718183225930061997636807/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (486529000158539841718183225930061997636807/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2916 BracketBatch0182.bracket2917 (486529000158539841718183225930061997636807/4000000000000000000000000000000000000000) (6413181878262474112054089123813389073993/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2916 BracketBatch0182.bracket2917
  (486529000158539841718183225930061997636807/4000000000000000000000000000000000000000) (6413181878262474112054089123813389073993/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2916
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2917
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1217798885237939408946524160122556568118333/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1217798885237939408946524160122556568118333/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (122076605872211856422273057671369109633003/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (122076605872211856422273057671369109633003/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (2438564943960057973169254736836247664448363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2438564943960057973169254736836247664448363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2917 BracketBatch0182.bracket2918 (2438564943960057973169254736836247664448363/20000000000000000000000000000000000000000) (3208459710613909445477574955666604085909/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2917 BracketBatch0182.bracket2918
  (2438564943960057973169254736836247664448363/20000000000000000000000000000000000000000) (3208459710613909445477574955666604085909/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2917
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2918
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1220766058722118564222730576713691096330027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1220766058722118564222730576713691096330027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (305936935414661891918139709316044194850459/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (305936935414661891918139709316044194850459/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (2444513800380766131895289413977867875731863/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2444513800380766131895289413977867875731863/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2918 BracketBatch0182.bracket2919 (2444513800380766131895289413977867875731863/20000000000000000000000000000000000000000) (6420665987813564935737667894262064392747/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2918 BracketBatch0182.bracket2919
  (2444513800380766131895289413977867875731863/20000000000000000000000000000000000000000) (6420665987813564935737667894262064392747/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2918
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2919
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1223747741658647567672558837264176779401833/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1223747741658647567672558837264176779401833/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1226744040734674273612130599725012505372621/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1226744040734674273612130599725012505372621/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1225245891196660920642344718494594642387227/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1225245891196660920642344718494594642387227/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0364.rows ScalarLogs0364.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2919 BracketBatch0182.bracket2920 (1225245891196660920642344718494594642387227/10000000000000000000000000000000000000000) (3212210809446900461076147048151988409053/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2919 BracketBatch0182.bracket2920
  (1225245891196660920642344718494594642387227/10000000000000000000000000000000000000000) (3212210809446900461076147048151988409053/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2919
