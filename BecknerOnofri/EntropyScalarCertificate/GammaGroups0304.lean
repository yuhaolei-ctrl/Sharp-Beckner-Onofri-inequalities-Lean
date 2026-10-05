import BecknerOnofri.EntropyScalarCertificate.Bessel0380
import BecknerOnofri.EntropyScalarCertificate.Bessel0381
import BecknerOnofri.EntropyScalarCertificate.Bessel0678
import BecknerOnofri.EntropyScalarCertificate.Bessel0679
import BecknerOnofri.EntropyScalarCertificate.Brackets0152
import BecknerOnofri.EntropyScalarCertificate.Logs0304
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2432
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (70384042286494077625607285349954329769273/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (70384042286494077625607285349954329769273/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (141082973998035393526309961234293017999343/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (141082973998035393526309961234293017999343/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (281851058571023548777524531934201677537889/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (281851058571023548777524531934201677537889/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2432 BracketBatch0152.bracket2433 (281851058571023548777524531934201677537889/10000000000000000000000000000000000000000) (1051534530720430390863160025575473905393/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2432 BracketBatch0152.bracket2433
  (281851058571023548777524531934201677537889/10000000000000000000000000000000000000000) (1051534530720430390863160025575473905393/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2432
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2433
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (282165947996070787052619922468586035998683/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (282165947996070787052619922468586035998683/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (7069964096720710079312221995725025035903/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7069964096720710079312221995725025035903/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (564964511864899190225108802297587037434803/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (564964511864899190225108802297587037434803/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2433 BracketBatch0152.bracket2434 (564964511864899190225108802297587037434803/20000000000000000000000000000000000000000) (4209357149626060267630312213081103339853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2433 BracketBatch0152.bracket2434
  (564964511864899190225108802297587037434803/20000000000000000000000000000000000000000) (4209357149626060267630312213081103339853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2433
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2434
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (282798563868828403172488879829001001436117/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (282798563868828403172488879829001001436117/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (56686807195312620548084566560901576627701/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56686807195312620548084566560901576627701/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (283116299922695752956455856316754442287311/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (283116299922695752956455856316754442287311/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2434 BracketBatch0152.bracket2435 (283116299922695752956455856316754442287311/10000000000000000000000000000000000000000) (4212583836803255632975086732767130719567/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2434 BracketBatch0152.bracket2435
  (283116299922695752956455856316754442287311/10000000000000000000000000000000000000000) (4212583836803255632975086732767130719567/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2434
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2435
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (141717017988281551370211416402253941569251/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (141717017988281551370211416402253941569251/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (17754523981590995853023836650369255673293/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17754523981590995853023836650369255673293/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (56750641968201903638880421921041597391119/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (56750641968201903638880421921041597391119/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2435 BracketBatch0152.bracket2436 (56750641968201903638880421921041597391119/2000000000000000000000000000000000000000) (4215818218684614261602181971180308382849/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2435 BracketBatch0152.bracket2436
  (56750641968201903638880421921041597391119/2000000000000000000000000000000000000000) (4215818218684614261602181971180308382849/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2435
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2436
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (56814476741091186729676277281181618154537/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56814476741091186729676277281181618154537/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (56942725323505266031011842300962194557209/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56942725323505266031011842300962194557209/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (56878601032298226380344059791071906355873/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (56878601032298226380344059791071906355873/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2436 BracketBatch0152.bracket2437 (56878601032298226380344059791071906355873/2000000000000000000000000000000000000000) (4219060329763979532721480052344007709349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2436 BracketBatch0152.bracket2437
  (56878601032298226380344059791071906355873/2000000000000000000000000000000000000000) (4219060329763979532721480052344007709349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2436
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2437
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (142356813308763165077529605752405486393021/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (142356813308763165077529605752405486393021/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (71339446113157569090512603386267530555047/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (71339446113157569090512603386267530555047/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (57007141107015660651710962504988109500623/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57007141107015660651710962504988109500623/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2437 BracketBatch0152.bracket2438 (57007141107015660651710962504988109500623/2000000000000000000000000000000000000000) (211115510237979731044379597866913918879/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2437 BracketBatch0152.bracket2438
  (57007141107015660651710962504988109500623/2000000000000000000000000000000000000000) (211115510237979731044379597866913918879/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2437
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2438
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (57071556890526055272410082709014024444037/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57071556890526055272410082709014024444037/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (286004877130485779441399983719327152484353/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (286004877130485779441399983719327152484353/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (285681330791558027901725198632198637352269/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (285681330791558027901725198632198637352269/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2438 BracketBatch0152.bracket2439 (285681330791558027901725198632198637352269/10000000000000000000000000000000000000000) (1056391969653996031701745768042853974693/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2438 BracketBatch0152.bracket2439
  (285681330791558027901725198632198637352269/10000000000000000000000000000000000000000) (1056391969653996031701745768042853974693/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2438
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2439
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (5720097542609715588827999674386543049687/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5720097542609715588827999674386543049687/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (286654924752726089071756276206746335258619/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (286654924752726089071756276206746335258619/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (572659801883211868513156259926073487742969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (572659801883211868513156259926073487742969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0304.rows ScalarLogs0304.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2439 BracketBatch0152.bracket2440 (572659801883211868513156259926073487742969/20000000000000000000000000000000000000000) (4228833386505854527754653638547087133203/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2439 BracketBatch0152.bracket2440
  (572659801883211868513156259926073487742969/20000000000000000000000000000000000000000) (4228833386505854527754653638547087133203/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2439
