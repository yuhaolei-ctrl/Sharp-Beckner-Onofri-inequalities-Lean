import BecknerOnofri.EntropyScalarCertificate.Bessel0215
import BecknerOnofri.EntropyScalarCertificate.Bessel0216
import BecknerOnofri.EntropyScalarCertificate.Bessel0596
import BecknerOnofri.EntropyScalarCertificate.Bessel0597
import BecknerOnofri.EntropyScalarCertificate.Brackets0086
import BecknerOnofri.EntropyScalarCertificate.Logs0172
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1376
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (64149928868925776767977627538264742163/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64149928868925776767977627538264742163/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (16463918876119529365747037332266829700231/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16463918876119529365747037332266829700231/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (32886300666564528218349309982062603693959/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32886300666564528218349309982062603693959/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1376 BracketBatch0086.bracket1377 (32886300666564528218349309982062603693959/20000000000000000000000000000000000000000) (152146998951878487040570856890334385297/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1376 BracketBatch0086.bracket1377
  (32886300666564528218349309982062603693959/20000000000000000000000000000000000000000) (152146998951878487040570856890334385297/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1376
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1377
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (4115979719029882341436759333066707425057/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4115979719029882341436759333066707425057/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (16505694708906078908779867525408559653429/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16505694708906078908779867525408559653429/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (32969613585025608274526904857675389353657/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32969613585025608274526904857675389353657/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1377 BracketBatch0086.bracket1378 (32969613585025608274526904857675389353657/20000000000000000000000000000000000000000) (2386299460217437942020241562372294383/39062500000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1377 BracketBatch0086.bracket1378
  (32969613585025608274526904857675389353657/20000000000000000000000000000000000000000) (2386299460217437942020241562372294383/39062500000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1377
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1378
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (8252847354453039454389933762704279826713/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8252847354453039454389933762704279826713/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (8257039362076891042465187667775654256329/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8257039362076891042465187667775654256329/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (8254943358264965248427560715239967041521/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8254943358264965248427560715239967041521/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1378 BracketBatch0086.bracket1379 (8254943358264965248427560715239967041521/5000000000000000000000000000000000000000) (307322419774637886787471366078317617379/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1378 BracketBatch0086.bracket1379
  (8254943358264965248427560715239967041521/5000000000000000000000000000000000000000) (307322419774637886787471366078317617379/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1378
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1379
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3302815744830756416986075067110261702531/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3302815744830756416986075067110261702531/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (16522472398161570067058922317492109015191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16522472398161570067058922317492109015191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (16518275561157676075994648826521708763923/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16518275561157676075994648826521708763923/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1379 BracketBatch0086.bracket1380 (16518275561157676075994648826521708763923/10000000000000000000000000000000000000000) (615111429906673761209485219126404976151/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1379 BracketBatch0086.bracket1380
  (16518275561157676075994648826521708763923/10000000000000000000000000000000000000000) (615111429906673761209485219126404976151/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1379
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1380
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (4130618099540392516764730579373027253797/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4130618099540392516764730579373027253797/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (8265437874622904506023621298530759518907/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8265437874622904506023621298530759518907/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (16526674073703689539553082457276814026501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16526674073703689539553082457276814026501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1380 BracketBatch0086.bracket1381 (16526674073703689539553082457276814026501/10000000000000000000000000000000000000000) (615578476651643928789868219966981158069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1380 BracketBatch0086.bracket1381
  (16526674073703689539553082457276814026501/10000000000000000000000000000000000000000) (615578476651643928789868219966981158069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1380
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1381
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (16530875749245809012047242597061519037811/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16530875749245809012047242597061519037811/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (16539288795767721546870246973771902738657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16539288795767721546870246973771902738657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (8267541136253382639729372392708355444117/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8267541136253382639729372392708355444117/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1381 BracketBatch0086.bracket1382 (8267541136253382639729372392708355444117/5000000000000000000000000000000000000000) (38502873777718578030332183003845464827/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1381 BracketBatch0086.bracket1382
  (8267541136253382639729372392708355444117/5000000000000000000000000000000000000000) (38502873777718578030332183003845464827/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1381
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1382
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (8269644397883860773435123486885951369327/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8269644397883860773435123486885951369327/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (3309542311226703600940610050911576599011/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3309542311226703600940610050911576599011/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (33087000351901239551573297228329785733709/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33087000351901239551573297228329785733709/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1382 BracketBatch0086.bracket1383 (33087000351901239551573297228329785733709/20000000000000000000000000000000000000000) (154128485485691353015810173019367498631/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1382 BracketBatch0086.bracket1383
  (33087000351901239551573297228329785733709/20000000000000000000000000000000000000000) (154128485485691353015810173019367498631/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1382
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1383
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4136927889033379501175762563639470748763/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4136927889033379501175762563639470748763/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (662245761951781124183539130959736642983/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (662245761951781124183539130959736642983/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (33103855604928046109291528528551299069627/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33103855604928046109291528528551299069627/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0172.rows ScalarLogs0172.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1383 BracketBatch0086.bracket1384 (33103855604928046109291528528551299069627/20000000000000000000000000000000000000000) (19280698806600101468517286680203024929/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1383 BracketBatch0086.bracket1384
  (33103855604928046109291528528551299069627/20000000000000000000000000000000000000000) (19280698806600101468517286680203024929/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1383
