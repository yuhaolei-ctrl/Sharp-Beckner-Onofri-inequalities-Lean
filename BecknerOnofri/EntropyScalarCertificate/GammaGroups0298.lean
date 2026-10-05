import BecknerOnofri.EntropyScalarCertificate.Bessel0372
import BecknerOnofri.EntropyScalarCertificate.Bessel0373
import BecknerOnofri.EntropyScalarCertificate.Bessel0675
import BecknerOnofri.EntropyScalarCertificate.Brackets0149
import BecknerOnofri.EntropyScalarCertificate.Logs0298
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2384
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (31788179676171660203682615069626880657719/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31788179676171660203682615069626880657719/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (50963731288730623989215547473437063893953/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50963731288730623989215547473437063893953/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (509124093853026401575538657924200364731517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (509124093853026401575538657924200364731517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2384 BracketBatch0149.bracket2385 (509124093853026401575538657924200364731517/20000000000000000000000000000000000000000) (162400518156814966478238210232026237681/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2384 BracketBatch0149.bracket2385
  (509124093853026401575538657924200364731517/20000000000000000000000000000000000000000) (162400518156814966478238210232026237681/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2384
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2385
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (127409328221826559973038868683592659734881/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (127409328221826559973038868683592659734881/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (255333961898777628198419879283255085084709/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (255333961898777628198419879283255085084709/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (510152618342430748144497616650440404554471/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (510152618342430748144497616650440404554471/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2385 BracketBatch0149.bracket2386 (510152618342430748144497616650440404554471/20000000000000000000000000000000000000000) (4062900642784551396301618940663607340597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2385 BracketBatch0149.bracket2386
  (510152618342430748144497616650440404554471/20000000000000000000000000000000000000000) (4062900642784551396301618940663607340597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2385
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2386
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (127666980949388814099209939641627542542353/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (127666980949388814099209939641627542542353/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (255851366522708960013791942820717441445803/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (255851366522708960013791942820717441445803/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (511185328421486588212211822103972526530509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (511185328421486588212211822103972526530509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2386 BracketBatch0149.bracket2387 (511185328421486588212211822103972526530509/20000000000000000000000000000000000000000) (2032897288204954809633667609679414182443/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2386 BracketBatch0149.bracket2387
  (511185328421486588212211822103972526530509/20000000000000000000000000000000000000000) (2032897288204954809633667609679414182443/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2386
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2387
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1279256832613544800068959714103587207229/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1279256832613544800068959714103587207229/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (128185441583737137496327349125766026812269/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128185441583737137496327349125766026812269/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (256111124845091617503223320536124747535169/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (256111124845091617503223320536124747535169/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2387 BracketBatch0149.bracket2388 (256111124845091617503223320536124747535169/10000000000000000000000000000000000000000) (508586847532282288431919826062645158013/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2387 BracketBatch0149.bracket2388
  (256111124845091617503223320536124747535169/10000000000000000000000000000000000000000) (508586847532282288431919826062645158013/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2387
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2388
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (51274176633494854998530939650306410724907/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (51274176633494854998530939650306410724907/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (128446262395114899034728034609191032610881/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128446262395114899034728034609191032610881/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (513263407957704073062110767469914118846297/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (513263407957704073062110767469914118846297/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2388 BracketBatch0149.bracket2389 (513263407957704073062110767469914118846297/20000000000000000000000000000000000000000) (4071601279942877337113279533057058357611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2388 BracketBatch0149.bracket2389
  (513263407957704073062110767469914118846297/20000000000000000000000000000000000000000) (4071601279942877337113279533057058357611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2388
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2389
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (256892524790229798069456069218382065221759/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (256892524790229798069456069218382065221759/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (6435407611358449039263143240891525958389/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6435407611358449039263143240891525958389/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (514308829244567759639981798854043103557319/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (514308829244567759639981798854043103557319/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2389 BracketBatch0149.bracket2390 (514308829244567759639981798854043103557319/20000000000000000000000000000000000000000) (2037257050614844790934863478592671307797/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2389 BracketBatch0149.bracket2390
  (514308829244567759639981798854043103557319/20000000000000000000000000000000000000000) (2037257050614844790934863478592671307797/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2389
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2390
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (257416304454337961570525729635661038335557/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (257416304454337961570525729635661038335557/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (257942235330457818016013693347667421215663/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (257942235330457818016013693347667421215663/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (25767926989239788979326971149166422977561/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25767926989239788979326971149166422977561/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2390 BracketBatch0149.bracket2391 (25767926989239788979326971149166422977561/1000000000000000000000000000000000000000) (407743327003844452343722760922541746581/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2390 BracketBatch0149.bracket2391
  (25767926989239788979326971149166422977561/1000000000000000000000000000000000000000) (407743327003844452343722760922541746581/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2390
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2391
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (12897111766522890900800684667383371060783/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12897111766522890900800684667383371060783/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (258470330697648914808276817297865085239941/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (258470330697648914808276817297865085239941/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (516412566028106732824290510645532506455601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (516412566028106732824290510645532506455601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0298.rows ScalarLogs0298.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2391 BracketBatch0149.bracket2392 (516412566028106732824290510645532506455601/20000000000000000000000000000000000000000) (255022425777744562137249631771253963919/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2391 BracketBatch0149.bracket2392
  (516412566028106732824290510645532506455601/20000000000000000000000000000000000000000) (255022425777744562137249631771253963919/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2391
