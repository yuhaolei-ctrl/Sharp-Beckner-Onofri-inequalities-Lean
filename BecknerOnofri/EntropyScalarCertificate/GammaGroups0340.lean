import BecknerOnofri.EntropyScalarCertificate.Bessel0425
import BecknerOnofri.EntropyScalarCertificate.Bessel0426
import BecknerOnofri.EntropyScalarCertificate.Bessel0701
import BecknerOnofri.EntropyScalarCertificate.Bessel0702
import BecknerOnofri.EntropyScalarCertificate.Brackets0170
import BecknerOnofri.EntropyScalarCertificate.Logs0340
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2720
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (792395212869800736321165042327881755041899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (792395212869800736321165042327881755041899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (398717139105673190281339972177641227831351/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (398717139105673190281339972177641227831351/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (1589829491081147116883844986683164210704601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1589829491081147116883844986683164210704601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2720 BracketBatch0170.bracket2721 (1589829491081147116883844986683164210704601/20000000000000000000000000000000000000000) (571678190342560114021771610368452200099/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2720 BracketBatch0170.bracket2721
  (1589829491081147116883844986683164210704601/20000000000000000000000000000000000000000) (571678190342560114021771610368452200099/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2720
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2721
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (797434278211346380562679944355282455662699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (797434278211346380562679944355282455662699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (802537947447068133723604598574949495041869/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (802537947447068133723604598574949495041869/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (199996528207301814285785567866278993838071/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (199996528207301814285785567866278993838071/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2721 BracketBatch0170.bracket2722 (199996528207301814285785567866278993838071/2500000000000000000000000000000000000000) (2862909721738906094253239591118212378963/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2721 BracketBatch0170.bracket2722
  (199996528207301814285785567866278993838071/2500000000000000000000000000000000000000) (2862909721738906094253239591118212378963/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2721
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2722
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (401268973723534066861802299287474747520933/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (401268973723534066861802299287474747520933/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (50481716935927607103715636492656849578419/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50481716935927607103715636492656849578419/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (161024541842190984738305478245745908829657/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (161024541842190984738305478245745908829657/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2722 BracketBatch0170.bracket2723 (161024541842190984738305478245745908829657/2000000000000000000000000000000000000000) (1433726168091939062678536138766094012217/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2722 BracketBatch0170.bracket2723
  (161024541842190984738305478245745908829657/2000000000000000000000000000000000000000) (1433726168091939062678536138766094012217/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2722
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2723
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (807707470974841713659450183882509593254701/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (807707470974841713659450183882509593254701/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (203236032917602440843915620175929500558893/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (203236032917602440843915620175929500558893/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1620651602645251477035112664586227595490273/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1620651602645251477035112664586227595490273/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2723 BracketBatch0170.bracket2724 (1620651602645251477035112664586227595490273/20000000000000000000000000000000000000000) (574403789656663647503228072563527565563/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2723 BracketBatch0170.bracket2724
  (1620651602645251477035112664586227595490273/20000000000000000000000000000000000000000) (574403789656663647503228072563527565563/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2723
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2724
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (812944131670409763375662480703718002235569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (812944131670409763375662480703718002235569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (204562311487187512795965108260176623777441/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (204562311487187512795965108260176623777441/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1631193377619159814559522913744424497345333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1631193377619159814559522913744424497345333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2724 BracketBatch0170.bracket2725 (1631193377619159814559522913744424497345333/20000000000000000000000000000000000000000) (5753219418687432676942807776742732681753/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2724 BracketBatch0170.bracket2725
  (1631193377619159814559522913744424497345333/20000000000000000000000000000000000000000) (5753219418687432676942807776742732681753/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2724
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2725
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (818249245948750051183860433040706495109761/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (818249245948750051183860433040706495109761/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (411812082433669892011073021027554174244377/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (411812082433669892011073021027554174244377/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (328374682163217967041201295019162968719703/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (328374682163217967041201295019162968719703/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2725 BracketBatch0170.bracket2726 (328374682163217967041201295019162968719703/4000000000000000000000000000000000000000) (2881224768502555122334273540539392449197/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2725 BracketBatch0170.bracket2726
  (328374682163217967041201295019162968719703/4000000000000000000000000000000000000000) (2881224768502555122334273540539392449197/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2725
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2726
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (823624164867339784022146042055108348488751/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (823624164867339784022146042055108348488751/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (414535137636629118930499410916574449221129/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (414535137636629118930499410916574449221129/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1652694440140598021883144863888257246931009/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1652694440140598021883144863888257246931009/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2726 BracketBatch0170.bracket2727 (1652694440140598021883144863888257246931009/20000000000000000000000000000000000000000) (5771728544943789720487332443343425490961/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2726 BracketBatch0170.bracket2727
  (1652694440140598021883144863888257246931009/20000000000000000000000000000000000000000) (5771728544943789720487332443343425490961/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2726
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2727
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (165814055054651647572199764366629779688451/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (165814055054651647572199764366629779688451/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (834589000996173493325415420292729186882017/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (834589000996173493325415420292729186882017/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (103978704766839483199150890132867380332767/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (103978704766839483199150890132867380332767/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0340.rows ScalarLogs0340.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2727 BracketBatch0170.bracket2728 (103978704766839483199150890132867380332767/1250000000000000000000000000000000000000) (1445264182632163980602496710321173705137/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2727 BracketBatch0170.bracket2728
  (103978704766839483199150890132867380332767/1250000000000000000000000000000000000000) (1445264182632163980602496710321173705137/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2727
