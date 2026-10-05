import BecknerOnofri.EntropyScalarCertificate.Bessel0093
import BecknerOnofri.EntropyScalarCertificate.Bessel0094
import BecknerOnofri.EntropyScalarCertificate.Bessel0095
import BecknerOnofri.EntropyScalarCertificate.Bessel0535
import BecknerOnofri.EntropyScalarCertificate.Bessel0536
import BecknerOnofri.EntropyScalarCertificate.Brackets0037
import BecknerOnofri.EntropyScalarCertificate.Brackets0038
import BecknerOnofri.EntropyScalarCertificate.Logs0075
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0600
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (35864547175855560558656594227096457239/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35864547175855560558656594227096457239/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (448831287349834583450825297807741776049/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (448831287349834583450825297807741776049/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1794276254096058180868065451292894983073/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1794276254096058180868065451292894983073/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0600 BracketBatch0037.bracket0601 (1794276254096058180868065451292894983073/10000000000000000000000000000000000000000) (765228862276521423127776692743486051/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0600 BracketBatch0037.bracket0601
  (1794276254096058180868065451292894983073/10000000000000000000000000000000000000000) (765228862276521423127776692743486051/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0600
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0601
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1795325149399338333803301191230967104193/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1795325149399338333803301191230967104193/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (898711585823210696032849173374416839569/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (898711585823210696032849173374416839569/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (3592748321045759725868999537979800783331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3592748321045759725868999537979800783331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0601 BracketBatch0037.bracket0602 (3592748321045759725868999537979800783331/20000000000000000000000000000000000000000) (384363693154837180213984665512903273/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0601 BracketBatch0037.bracket0602
  (3592748321045759725868999537979800783331/20000000000000000000000000000000000000000) (384363693154837180213984665512903273/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0601
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0602
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (359484634329284278413139669349766735827/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (359484634329284278413139669349766735827/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (449880356460890812924941154628897750669/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (449880356460890812924941154628897750669/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (3596944597489984643765462965264424681811/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3596944597489984643765462965264424681811/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0602 BracketBatch0037.bracket0603 (3596944597489984643765462965264424681811/20000000000000000000000000000000000000000) (7722379636532208662798654153601361/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0602 BracketBatch0037.bracket0603
  (3596944597489984643765462965264424681811/20000000000000000000000000000000000000000) (7722379636532208662798654153601361/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0602
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0603
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1799521425843563251699764618515591002673/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1799521425843563251699764618515591002673/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (900809956150237282223184710325749667021/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (900809956150237282223184710325749667021/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (720228267628807563229226807833418067343/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (720228267628807563229226807833418067343/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0603 BracketBatch0037.bracket0604 (720228267628807563229226807833418067343/4000000000000000000000000000000000000000) (77576062249456357443499280862715777/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0603 BracketBatch0037.bracket0604
  (720228267628807563229226807833418067343/4000000000000000000000000000000000000000) (77576062249456357443499280862715777/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0603
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0604
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1801619912300474564446369420651499334039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1801619912300474564446369420651499334039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1803718631327040866128023060306468174873/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1803718631327040866128023060306468174873/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (225333658976719714410899530059872969307/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (225333658976719714410899530059872969307/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0604 BracketBatch0037.bracket0605 (225333658976719714410899530059872969307/1250000000000000000000000000000000000000) (389647695528573134600775406256376453/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0604 BracketBatch0037.bracket0605
  (225333658976719714410899530059872969307/1250000000000000000000000000000000000000) (389647695528573134600775406256376453/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0604
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0605
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (180371863132704086612802306030646817487/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (180371863132704086612802306030646817487/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1805817583233322858298148441457245817811/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1805817583233322858298148441457245817811/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (3609536214560363724426171501763713992681/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3609536214560363724426171501763713992681/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0605 BracketBatch0037.bracket0606 (3609536214560363724426171501763713992681/20000000000000000000000000000000000000000) (782842297600468983382898462794641211/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0605 BracketBatch0037.bracket0606
  (3609536214560363724426171501763713992681/20000000000000000000000000000000000000000) (782842297600468983382898462794641211/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0605
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0606
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (112863598952082678643634277591077863613/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (112863598952082678643634277591077863613/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (903958384164778345109878610147976465419/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (903958384164778345109878610147976465419/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (1806867175781439774258952830876599374323/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1806867175781439774258952830876599374323/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0606 BracketBatch0037.bracket0607 (1806867175781439774258952830876599374323/10000000000000000000000000000000000000000) (393200685210051559672020408611383721/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0606 BracketBatch0037.bracket0607
  (1806867175781439774258952830876599374323/10000000000000000000000000000000000000000) (393200685210051559672020408611383721/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0606
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0607
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (361583353665911338043951444059190586167/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (361583353665911338043951444059190586167/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1810016186926154241174179240862648395797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1810016186926154241174179240862648395797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (452241619406963866424242057644825165829/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (452241619406963866424242057644825165829/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0075.rows ScalarLogs0075.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0607 BracketBatch0038.bracket0608 (452241619406963866424242057644825165829/2500000000000000000000000000000000000000) (394986318923853296614963320997618759/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0607 BracketBatch0038.bracket0608
  (452241619406963866424242057644825165829/2500000000000000000000000000000000000000) (394986318923853296614963320997618759/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0607
