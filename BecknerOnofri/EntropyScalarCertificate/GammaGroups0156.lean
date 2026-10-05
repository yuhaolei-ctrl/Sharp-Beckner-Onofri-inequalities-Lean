module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0195
public import BecknerOnofri.EntropyScalarCertificate.Bessel0196
public import BecknerOnofri.EntropyScalarCertificate.Bessel0586
public import BecknerOnofri.EntropyScalarCertificate.Bessel0587
public import BecknerOnofri.EntropyScalarCertificate.Brackets0078
public import BecknerOnofri.EntropyScalarCertificate.Logs0156
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1248
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (2767815047622077949280174853953744683057/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2767815047622077949280174853953744683057/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (11107755701693225662405670890518078062099/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11107755701693225662405670890518078062099/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (22179015892181537459526370306333056794327/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22179015892181537459526370306333056794327/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1248 BracketBatch0078.bracket1249 (22179015892181537459526370306333056794327/20000000000000000000000000000000000000000) (301298833231489687335802365550892147397/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1248 BracketBatch0078.bracket1249
  (22179015892181537459526370306333056794327/20000000000000000000000000000000000000000) (301298833231489687335802365550892147397/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1248
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1249
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (694234731355826603900354430657379878881/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (694234731355826603900354430657379878881/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (5572236525545485318663156395303155112953/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5572236525545485318663156395303155112953/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (11126114376392098149865991840562194144001/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11126114376392098149865991840562194144001/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1249 BracketBatch0078.bracket1250 (11126114376392098149865991840562194144001/10000000000000000000000000000000000000000) (4740178466089911098426096368628406611/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1249 BracketBatch0078.bracket1250
  (11126114376392098149865991840562194144001/10000000000000000000000000000000000000000) (4740178466089911098426096368628406611/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1249
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1250
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (11144473051090970637326312790606310225903/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11144473051090970637326312790606310225903/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (11181414843287787218142020687676199096929/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11181414843287787218142020687676199096929/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1395367993398672365966770842392656832677/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1395367993398672365966770842392656832677/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1250 BracketBatch0078.bracket1251 (1395367993398672365966770842392656832677/1250000000000000000000000000000000000000) (30545836130424512032092936965207589617/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1250 BracketBatch0078.bracket1251
  (1395367993398672365966770842392656832677/1250000000000000000000000000000000000000) (30545836130424512032092936965207589617/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1250
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1251
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (5590707421643893609071010343838099548463/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5590707421643893609071010343838099548463/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (2804645931198673061803046010958943371157/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2804645931198673061803046010958943371157/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (11199999284041239732677102365755986290777/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11199999284041239732677102365755986290777/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1251 BracketBatch0078.bracket1252 (11199999284041239732677102365755986290777/10000000000000000000000000000000000000000) (307559780489391664740245628669202670363/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1251 BracketBatch0078.bracket1252
  (11199999284041239732677102365755986290777/10000000000000000000000000000000000000000) (307559780489391664740245628669202670363/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1251
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1252
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (89748669798357537977697472350686187877/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89748669798357537977697472350686187877/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2813995596218220891392209312296648307031/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2813995596218220891392209312296648307031/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (22474566109667575812781021293022366712749/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22474566109667575812781021293022366712749/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1252 BracketBatch0078.bracket1253 (22474566109667575812781021293022366712749/20000000000000000000000000000000000000000) (309675809973783346935823521304159333273/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1252 BracketBatch0078.bracket1253
  (22474566109667575812781021293022366712749/20000000000000000000000000000000000000000) (309675809973783346935823521304159333273/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1252
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1253
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (11255982384872883565568837249186593228121/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11255982384872883565568837249186593228121/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (11293613556399355203036039132596547419419/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11293613556399355203036039132596547419419/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1127479797063611938430243819089157032377/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1127479797063611938430243819089157032377/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1253 BracketBatch0078.bracket1254 (1127479797063611938430243819089157032377/1000000000000000000000000000000000000000) (155903291065963945494133294215947375031/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1253 BracketBatch0078.bracket1254
  (1127479797063611938430243819089157032377/1000000000000000000000000000000000000000) (155903291065963945494133294215947375031/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1253
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1254
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1411701694549919400379504891574568427427/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1411701694549919400379504891574568427427/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (11331480016753275586185993844087619051749/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11331480016753275586185993844087619051749/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (4525018714630526157844406595336833294233/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4525018714630526157844406595336833294233/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1254 BracketBatch0078.bracket1255 (4525018714630526157844406595336833294233/4000000000000000000000000000000000000000) (313952231156672133601076161921574942519/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1254 BracketBatch0078.bracket1255
  (4525018714630526157844406595336833294233/4000000000000000000000000000000000000000) (313952231156672133601076161921574942519/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1254
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1255
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (5665740008376637793092996922043809525873/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5665740008376637793092996922043809525873/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (5684792294361849042305299479073498201871/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5684792294361849042305299479073498201871/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (88676033615144428401549190633728966623/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (88676033615144428401549190633728966623/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0156.rows ScalarLogs0156.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1255 BracketBatch0078.bracket1256 (88676033615144428401549190633728966623/78125000000000000000000000000000000000) (79028223273074977573106239956391742661/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1255 BracketBatch0078.bracket1256
  (88676033615144428401549190633728966623/78125000000000000000000000000000000000) (79028223273074977573106239956391742661/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1255
