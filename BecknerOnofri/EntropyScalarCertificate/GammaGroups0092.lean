import BecknerOnofri.EntropyScalarCertificate.Bessel0115
import BecknerOnofri.EntropyScalarCertificate.Bessel0116
import BecknerOnofri.EntropyScalarCertificate.Bessel0546
import BecknerOnofri.EntropyScalarCertificate.Bessel0547
import BecknerOnofri.EntropyScalarCertificate.Brackets0046
import BecknerOnofri.EntropyScalarCertificate.Logs0092
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0736
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (446789984824594567647307868549632654247/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (446789984824594567647307868549632654247/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (89788670336716855435255094005061157111/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89788670336716855435255094005061157111/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (447866668254089422411791669287469219901/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (447866668254089422411791669287469219901/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0736 BracketBatch0046.bracket0737 (447866668254089422411791669287469219901/2000000000000000000000000000000000000000) (890822839990591224932709060085794191/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0736 BracketBatch0046.bracket0737
  (447866668254089422411791669287469219901/2000000000000000000000000000000000000000) (890822839990591224932709060085794191/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0736
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0737
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (561179189604480346470344337531632231943/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (561179189604480346470344337531632231943/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (225549112923494286403914302219123373051/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (225549112923494286403914302219123373051/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2250103943826432124960260186158881329141/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2250103943826432124960260186158881329141/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0737 BracketBatch0046.bracket0738 (2250103943826432124960260186158881329141/10000000000000000000000000000000000000000) (363018423757380829478217575565916133/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0737 BracketBatch0046.bracket0738
  (2250103943826432124960260186158881329141/10000000000000000000000000000000000000000) (363018423757380829478217575565916133/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0737
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0738
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (2255491129234942864039143022191233730507/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2255491129234942864039143022191233730507/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (453254616159336322537485152497215914409/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (453254616159336322537485152497215914409/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (565220526253953059590821098084664162819/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (565220526253953059590821098084664162819/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0738 BracketBatch0046.bracket0739 (565220526253953059590821098084664162819/2500000000000000000000000000000000000000) (462252335751938487288624748664760983/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0738 BracketBatch0046.bracket0739
  (565220526253953059590821098084664162819/2500000000000000000000000000000000000000) (462252335751938487288624748664760983/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0738
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0739
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1133136540398340806343712881243039786021/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1133136540398340806343712881243039786021/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1138531328739142751261186351620390543861/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1138531328739142751261186351620390543861/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1135833934568741778802449616431715164941/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1135833934568741778802449616431715164941/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0739 BracketBatch0046.bracket0740 (1135833934568741778802449616431715164941/5000000000000000000000000000000000000000) (941700941663403099411985563431200237/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0739 BracketBatch0046.bracket0740
  (1135833934568741778802449616431715164941/5000000000000000000000000000000000000000) (941700941663403099411985563431200237/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0739
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0740
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (2277062657478285502522372703240781087719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2277062657478285502522372703240781087719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2287859903808563194366995645940709898127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2287859903808563194366995645940709898127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (2282461280643424348444684174590745492923/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2282461280643424348444684174590745492923/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0740 BracketBatch0046.bracket0741 (2282461280643424348444684174590745492923/10000000000000000000000000000000000000000) (959137147665556190396190825313068853/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0740 BracketBatch0046.bracket0741
  (2282461280643424348444684174590745492923/10000000000000000000000000000000000000000) (959137147665556190396190825313068853/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0740
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0741
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (571964975952140798591748911485177474531/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (571964975952140798591748911485177474531/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (57466621611778731960567535405943975011/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57466621611778731960567535405943975011/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1146631192069928118197424265544617224641/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1146631192069928118197424265544617224641/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0741 BracketBatch0046.bracket0742 (1146631192069928118197424265544617224641/5000000000000000000000000000000000000000) (1953631159576529038253452691412461159/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0741 BracketBatch0046.bracket0742
  (1146631192069928118197424265544617224641/5000000000000000000000000000000000000000) (1953631159576529038253452691412461159/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0741
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0742
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2298664864471149278422701416237759000437/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2298664864471149278422701416237759000437/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1154738792152838685220579029260169362413/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1154738792152838685220579029260169362413/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (4608142448776826648863859474758097725263/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4608142448776826648863859474758097725263/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0742 BracketBatch0046.bracket0743 (4608142448776826648863859474758097725263/20000000000000000000000000000000000000000) (1989477081653008358726141955616021043/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0742 BracketBatch0046.bracket0743
  (4608142448776826648863859474758097725263/20000000000000000000000000000000000000000) (1989477081653008358726141955616021043/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0742
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0743
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2309477584305677370441158058520338724823/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2309477584305677370441158058520338724823/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (464059621661792248533952457568297888151/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (464059621661792248533952457568297888151/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2314887846307319306555460173180914082789/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2314887846307319306555460173180914082789/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0092.rows ScalarLogs0092.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0046.bracket0743 BracketBatch0046.bracket0744 (2314887846307319306555460173180914082789/10000000000000000000000000000000000000000) (2025816692250354301097360037131327173/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0046.bracket0743 BracketBatch0046.bracket0744
  (2314887846307319306555460173180914082789/10000000000000000000000000000000000000000) (2025816692250354301097360037131327173/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0743
