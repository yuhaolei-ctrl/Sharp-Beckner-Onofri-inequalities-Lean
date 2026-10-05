import BecknerOnofri.EntropyScalarCertificate.Bessel0150
import BecknerOnofri.EntropyScalarCertificate.Bessel0151
import BecknerOnofri.EntropyScalarCertificate.Bessel0563
import BecknerOnofri.EntropyScalarCertificate.Bessel0564
import BecknerOnofri.EntropyScalarCertificate.Brackets0060
import BecknerOnofri.EntropyScalarCertificate.Logs0120
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0960
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (4938296343552237845696418469002681427813/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4938296343552237845696418469002681427813/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (990461966273830083564326761966464677649/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (990461966273830083564326761966464677649/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (4945303087460694131759026139417502408029/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4945303087460694131759026139417502408029/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0960 BracketBatch0060.bracket0961 (4945303087460694131759026139417502408029/10000000000000000000000000000000000000000) (32376731031349460030531485809942527119/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0960 BracketBatch0060.bracket0961
  (4945303087460694131759026139417502408029/10000000000000000000000000000000000000000) (32376731031349460030531485809942527119/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0960
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0961
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2476154915684575208910816904916161694121/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2476154915684575208910816904916161694121/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1241587015721921374887990825935689164057/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1241587015721921374887990825935689164057/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (991865789425683591737359711357508004447/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (991865789425683591737359711357508004447/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0961 BracketBatch0060.bracket0962 (991865789425683591737359711357508004447/2000000000000000000000000000000000000000) (16342551428126458501151512284859953633/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0961 BracketBatch0060.bracket0962
  (991865789425683591737359711357508004447/2000000000000000000000000000000000000000) (16342551428126458501151512284859953633/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0961
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0962
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (198653922515507419982078532149710266249/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (198653922515507419982078532149710266249/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2490205586964411619729820744760623424381/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2490205586964411619729820744760623424381/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (9946759236816508739011604793264003504987/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9946759236816508739011604793264003504987/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0962 BracketBatch0060.bracket0963 (9946759236816508739011604793264003504987/20000000000000000000000000000000000000000) (6599157453611787561938469347817285907/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0962 BracketBatch0060.bracket0963
  (9946759236816508739011604793264003504987/20000000000000000000000000000000000000000) (6599157453611787561938469347817285907/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0962
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0963
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (4980411173928823239459641489521246848759/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4980411173928823239459641489521246848759/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (4994499301223486889923070969890375647903/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4994499301223486889923070969890375647903/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (4987455237576155064691356229705811248331/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4987455237576155064691356229705811248331/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0963 BracketBatch0060.bracket0964 (4987455237576155064691356229705811248331/10000000000000000000000000000000000000000) (33308797661039249486269451787622215213/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0963 BracketBatch0060.bracket0964
  (4987455237576155064691356229705811248331/10000000000000000000000000000000000000000) (33308797661039249486269451787622215213/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0963
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0964
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (49944993012234868899230709698903756479/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49944993012234868899230709698903756479/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (5008612582420942333274794997557953898167/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5008612582420942333274794997557953898167/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (10003111883644429223197865967448329546067/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10003111883644429223197865967448329546067/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0964 BracketBatch0060.bracket0965 (10003111883644429223197865967448329546067/20000000000000000000000000000000000000000) (33624147495881442041644837924774055569/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0964 BracketBatch0060.bracket0965
  (10003111883644429223197865967448329546067/20000000000000000000000000000000000000000) (33624147495881442041644837924774055569/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0964
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0965
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1252153145605235583318698749389488474541/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1252153145605235583318698749389488474541/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2511375578048645455038089304302904063171/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2511375578048645455038089304302904063171/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (5015681869259116621675486803081881012253/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5015681869259116621675486803081881012253/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0965 BracketBatch0060.bracket0966 (5015681869259116621675486803081881012253/10000000000000000000000000000000000000000) (271534802400936252093069879502170477/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0965 BracketBatch0060.bracket0966
  (5015681869259116621675486803081881012253/10000000000000000000000000000000000000000) (271534802400936252093069879502170477/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0965
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0966
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (5022751156097290910076178608605808126339/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5022751156097290910076178608605808126339/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (5036915161764056782256426867029040718469/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5036915161764056782256426867029040718469/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1257458289732668461541575684454356105601/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1257458289732668461541575684454356105601/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0966 BracketBatch0060.bracket0967 (1257458289732668461541575684454356105601/2500000000000000000000000000000000000000) (34261919668553887798037713338113168031/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0966 BracketBatch0060.bracket0967
  (1257458289732668461541575684454356105601/2500000000000000000000000000000000000000) (34261919668553887798037713338113168031/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0966
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0967
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2518457580882028391128213433514520359233/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2518457580882028391128213433514520359233/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2525552369938435041278950192010373098677/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2525552369938435041278950192010373098677/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (504400995082046343240716362552489345791/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (504400995082046343240716362552489345791/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0120.rows ScalarLogs0120.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0967 BracketBatch0060.bracket0968 (504400995082046343240716362552489345791/1000000000000000000000000000000000000000) (34584369263713083081351646905148036831/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0967 BracketBatch0060.bracket0968
  (504400995082046343240716362552489345791/1000000000000000000000000000000000000000) (34584369263713083081351646905148036831/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0967
