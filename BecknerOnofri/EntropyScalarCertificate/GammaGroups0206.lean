import BecknerOnofri.EntropyScalarCertificate.Bessel0257
import BecknerOnofri.EntropyScalarCertificate.Bessel0258
import BecknerOnofri.EntropyScalarCertificate.Bessel0617
import BecknerOnofri.EntropyScalarCertificate.Bessel0618
import BecknerOnofri.EntropyScalarCertificate.Brackets0103
import BecknerOnofri.EntropyScalarCertificate.Logs0206
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1648
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4797761916904388958669743730859941253693/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4797761916904388958669743730859941253693/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (9601442409542620785243941065534392561613/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9601442409542620785243941065534392561613/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (19196966243351398702583428527254275068999/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19196966243351398702583428527254275068999/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1648 BracketBatch0103.bracket1649 (19196966243351398702583428527254275068999/10000000000000000000000000000000000000000) (379815791352145906686211614687709850179/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1648 BracketBatch0103.bracket1649
  (19196966243351398702583428527254275068999/10000000000000000000000000000000000000000) (379815791352145906686211614687709850179/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1648
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1649
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (19202884819085241570487882131068785123223/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19202884819085241570487882131068785123223/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1921473875043328726873866920469753884583/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1921473875043328726873866920469753884583/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (38417623569518528839226551335766323969053/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38417623569518528839226551335766323969053/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1649 BracketBatch0103.bracket1650 (38417623569518528839226551335766323969053/20000000000000000000000000000000000000000) (380124941485015171371474789573936390949/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1649 BracketBatch0103.bracket1650
  (38417623569518528839226551335766323969053/20000000000000000000000000000000000000000) (380124941485015171371474789573936390949/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1649
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1650
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (19214738750433287268738669204697538845827/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19214738750433287268738669204697538845827/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (9613304749393710418054663851719202704697/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9613304749393710418054663851719202704697/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (38441348249220708104847996908135944255221/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38441348249220708104847996908135944255221/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1650 BracketBatch0103.bracket1651 (38441348249220708104847996908135944255221/20000000000000000000000000000000000000000) (38043443547281568010655694290047721861/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1650 BracketBatch0103.bracket1651
  (38441348249220708104847996908135944255221/20000000000000000000000000000000000000000) (38043443547281568010655694290047721861/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1650
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1651
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (19226609498787420836109327703438405409391/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19226609498787420836109327703438405409391/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (9619248550688879603727119896877351121833/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9619248550688879603727119896877351121833/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (38465106600165180043563567497193107653057/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38465106600165180043563567497193107653057/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1651 BracketBatch0103.bracket1652 (38465106600165180043563567497193107653057/20000000000000000000000000000000000000000) (1522977095451163561364193148685921567/20000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1651 BracketBatch0103.bracket1652
  (38465106600165180043563567497193107653057/20000000000000000000000000000000000000000) (1522977095451163561364193148685921567/20000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1651
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1652
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (19238497101377759207454239793754702243663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19238497101377759207454239793754702243663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (19250401595539161439224326046088701155427/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19250401595539161439224326046088701155427/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (3848889869691692064667856583984340339909/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3848889869691692064667856583984340339909/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1652 BracketBatch0103.bracket1653 (3848889869691692064667856583984340339909/2000000000000000000000000000000000000000) (30484356576258317609103745107732643443/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1652 BracketBatch0103.bracket1653
  (3848889869691692064667856583984340339909/2000000000000000000000000000000000000000) (30484356576258317609103745107732643443/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1652
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1653
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (601575049860598794975760188940271911107/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (601575049860598794975760188940271911107/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (9631161509355791615322856100671679969443/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9631161509355791615322856100671679969443/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (3851272461425074466987003824743206109431/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3851272461425074466987003824743206109431/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1653 BracketBatch0103.bracket1654 (3851272461425074466987003824743206109431/2000000000000000000000000000000000000000) (381364986043464965580402283177442482549/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1653 BracketBatch0103.bracket1654
  (3851272461425074466987003824743206109431/2000000000000000000000000000000000000000) (381364986043464965580402283177442482549/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1653
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1654
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (19262323018711583230645712201343359938883/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19262323018711583230645712201343359938883/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (770970456337617315185575468516982330517/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (770970456337617315185575468516982330517/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (2408536526697001006892818682141744887613/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2408536526697001006892818682141744887613/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1654 BracketBatch0103.bracket1655 (2408536526697001006892818682141744887613/1250000000000000000000000000000000000000) (763351721867765949121777922588909206249/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1654 BracketBatch0103.bracket1655
  (2408536526697001006892818682141744887613/1250000000000000000000000000000000000000) (763351721867765949121777922588909206249/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1654
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1655
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (9637130704220216439819693356462279131461/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9637130704220216439819693356462279131461/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (19286216802376928680505300634184477058901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19286216802376928680505300634184477058901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (38560478210817361560144687347109035321823/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38560478210817361560144687347109035321823/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0206.rows ScalarLogs0206.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0103.bracket1655 BracketBatch0103.bracket1656 (38560478210817361560144687347109035321823/20000000000000000000000000000000000000000) (6111793318814693218255637563091031813/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0103.bracket1655 BracketBatch0103.bracket1656
  (38560478210817361560144687347109035321823/20000000000000000000000000000000000000000) (6111793318814693218255637563091031813/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1655
