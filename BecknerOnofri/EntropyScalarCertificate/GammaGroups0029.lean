import BecknerOnofri.EntropyScalarCertificate.Bessel0036
import BecknerOnofri.EntropyScalarCertificate.Bessel0037
import BecknerOnofri.EntropyScalarCertificate.Bessel0507
import BecknerOnofri.EntropyScalarCertificate.Brackets0014
import BecknerOnofri.EntropyScalarCertificate.Brackets0015
import BecknerOnofri.EntropyScalarCertificate.Logs0029
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0232
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1034496294725906683581766332811330774273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1034496294725906683581766332811330774273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1036528597407667584616175741380462835019/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1036528597407667584616175741380462835019/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (517756223033393567049485518547948402323/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (517756223033393567049485518547948402323/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0232 BracketBatch0014.bracket0233 (517756223033393567049485518547948402323/5000000000000000000000000000000000000000) (21825849114649660226941281959257409/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0232 BracketBatch0014.bracket0233
  (517756223033393567049485518547948402323/5000000000000000000000000000000000000000) (21825849114649660226941281959257409/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0232
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0233
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (129566074675958448077021967672557854377/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (129566074675958448077021967672557854377/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (519280513770692922864263339331025015609/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (519280513770692922864263339331025015609/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (1037544812474526715172351210021256433117/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1037544812474526715172351210021256433117/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0233 BracketBatch0014.bracket0234 (1037544812474526715172351210021256433117/10000000000000000000000000000000000000000) (21997193484055444220939476228100217/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0233 BracketBatch0014.bracket0234
  (1037544812474526715172351210021256433117/10000000000000000000000000000000000000000) (21997193484055444220939476228100217/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0233
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0234
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (207712205508277169145705335732410006243/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (207712205508277169145705335732410006243/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (208118717077827207671711406256335085709/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (208118717077827207671711406256335085709/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (25989432661631523551088546374296568247/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25989432661631523551088546374296568247/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0234 BracketBatch0014.bracket0235 (25989432661631523551088546374296568247/250000000000000000000000000000000000000) (17735633837124169017321495166007239/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0234 BracketBatch0014.bracket0235
  (25989432661631523551088546374296568247/250000000000000000000000000000000000000) (17735633837124169017321495166007239/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0234
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0235
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (520296792694568019179278515640837714271/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (520296792694568019179278515640837714271/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1042626271213081470963472558641099003739/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1042626271213081470963472558641099003739/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (2083219856602217509322029589922774432281/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2083219856602217509322029589922774432281/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0235 BracketBatch0014.bracket0236 (2083219856602217509322029589922774432281/20000000000000000000000000000000000000000) (4468579898958506670580732027511677/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0235 BracketBatch0014.bracket0236
  (2083219856602217509322029589922774432281/20000000000000000000000000000000000000000) (4468579898958506670580732027511677/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0235
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0236
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (130328283901635183870434069830137375467/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (130328283901635183870434069830137375467/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (261164771318868596358510502185702094099/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (261164771318868596358510502185702094099/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (521821339122138964099378641845976845033/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (521821339122138964099378641845976845033/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0236 BracketBatch0014.bracket0237 (521821339122138964099378641845976845033/5000000000000000000000000000000000000000) (22517269030283722955652766035732987/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0236 BracketBatch0014.bracket0237
  (521821339122138964099378641845976845033/5000000000000000000000000000000000000000) (22517269030283722955652766035732987/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0236
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0237
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1044659085275474385434042008742808376393/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1044659085275474385434042008742808376393/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1046692027838656153660967983092238730919/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1046692027838656153660967983092238730919/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (130709444569633158693438124489690444207/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (130709444569633158693438124489690444207/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0237 BracketBatch0014.bracket0238 (130709444569633158693438124489690444207/1250000000000000000000000000000000000000) (22692654861919799747609984620115409/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0237 BracketBatch0014.bracket0238
  (130709444569633158693438124489690444207/1250000000000000000000000000000000000000) (22692654861919799747609984620115409/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0237
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0238
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (261673006959664038415241995773059682729/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (261673006959664038415241995773059682729/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1048725099165057474251898578824300728333/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1048725099165057474251898578824300728333/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (2095417127003713627912866561916539459249/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2095417127003713627912866561916539459249/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0238 BracketBatch0014.bracket0239 (2095417127003713627912866561916539459249/20000000000000000000000000000000000000000) (91476243826873845927577726444597963/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0238 BracketBatch0014.bracket0239
  (2095417127003713627912866561916539459249/20000000000000000000000000000000000000000) (91476243826873845927577726444597963/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0238
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0239
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (104872509916505747425189857882430072833/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (104872509916505747425189857882430072833/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1050758299517198569399445303857116756923/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1050758299517198569399445303857116756923/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (2099483398682256043651343882681417485253/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2099483398682256043651343882681417485253/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0029.rows ScalarLogs0029.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0239 BracketBatch0015.bracket0240 (2099483398682256043651343882681417485253/20000000000000000000000000000000000000000) (9218596515870423662975588277016611/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0239 BracketBatch0015.bracket0240
  (2099483398682256043651343882681417485253/20000000000000000000000000000000000000000) (9218596515870423662975588277016611/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0239
