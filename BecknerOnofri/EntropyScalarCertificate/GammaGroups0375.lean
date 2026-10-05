module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0468
public import BecknerOnofri.EntropyScalarCertificate.Bessel0469
public import BecknerOnofri.EntropyScalarCertificate.Bessel0470
public import BecknerOnofri.EntropyScalarCertificate.Bessel0723
public import BecknerOnofri.EntropyScalarCertificate.Brackets0187
public import BecknerOnofri.EntropyScalarCertificate.Brackets0188
public import BecknerOnofri.EntropyScalarCertificate.Logs0375
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3000
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (38141083289676661025054724908242831211571/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38141083289676661025054724908242831211571/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1530305065999748509280795224742163650571509/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1530305065999748509280795224742163650571509/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (3055948397586814950282984221071876899034349/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3055948397586814950282984221071876899034349/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3000 BracketBatch0187.bracket3001 (3055948397586814950282984221071876899034349/20000000000000000000000000000000000000000) (6763055376762555034100164693473280728941/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3000 BracketBatch0187.bracket3001
  (3055948397586814950282984221071876899034349/20000000000000000000000000000000000000000) (6763055376762555034100164693473280728941/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3000
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3001
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (765152532999874254640397612371081825285753/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (765152532999874254640397612371081825285753/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (767497700034141831417362835352573651305699/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (767497700034141831417362835352573651305699/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (383162558258504021514440111930913869147863/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (383162558258504021514440111930913869147863/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3001 BracketBatch0187.bracket3002 (383162558258504021514440111930913869147863/2500000000000000000000000000000000000000) (338386121352676789225055829872012935789/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3001 BracketBatch0187.bracket3002
  (383162558258504021514440111930913869147863/2500000000000000000000000000000000000000) (338386121352676789225055829872012935789/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3001
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3002
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (306999080013656732566945134141029460522279/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (306999080013656732566945134141029460522279/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (61588583911579717764243765143632188528549/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61588583911579717764243765143632188528549/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (19216937486611103793380123745599700098907/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19216937486611103793380123745599700098907/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3002 BracketBatch0187.bracket3003 (19216937486611103793380123745599700098907/125000000000000000000000000000000000000) (1693100763867725792630680678631789920049/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3002 BracketBatch0187.bracket3003
  (19216937486611103793380123745599700098907/125000000000000000000000000000000000000) (1693100763867725792630680678631789920049/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3002
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3003
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (769857298894746472053047064295402356606861/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (769857298894746472053047064295402356606861/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (308892585283883481714782799598968600791353/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (308892585283883481714782799598968600791353/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (3084177524208910352680008126585647717170487/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3084177524208910352680008126585647717170487/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3003 BracketBatch0187.bracket3004 (3084177524208910352680008126585647717170487/20000000000000000000000000000000000000000) (677709733280273138922239045873906737027/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3003 BracketBatch0187.bracket3004
  (3084177524208910352680008126585647717170487/20000000000000000000000000000000000000000) (677709733280273138922239045873906737027/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3003
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3004
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (772231463209708704286956998997421501978381/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (772231463209708704286956998997421501978381/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (61969626260950817877492437056708070058621/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61969626260950817877492437056708070058621/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (3093703582943187855511224924412544755422287/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3093703582943187855511224924412544755422287/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3004 BracketBatch0187.bracket3005 (3093703582943187855511224924412544755422287/20000000000000000000000000000000000000000) (6781805330297399305243919850058591996173/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3004 BracketBatch0187.bracket3005
  (3093703582943187855511224924412544755422287/20000000000000000000000000000000000000000) (6781805330297399305243919850058591996173/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3004
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3005
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (774620328261885223468655463208850875732761/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (774620328261885223468655463208850875732761/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (388512015507332553170257835914776971806047/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (388512015507332553170257835914776971806047/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (310328871855310065961834227007680963868971/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (310328871855310065961834227007680963868971/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3005 BracketBatch0187.bracket3006 (310328871855310065961834227007680963868971/2000000000000000000000000000000000000000) (6786527119665722861269494223121426473289/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3005 BracketBatch0187.bracket3006
  (310328871855310065961834227007680963868971/2000000000000000000000000000000000000000) (6786527119665722861269494223121426473289/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3005
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3006
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (310809612405866042536206268731821577444837/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (310809612405866042536206268731821577444837/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1558885420276292655763670785875129099845347/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1558885420276292655763670785875129099845347/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (778233370576405717111175532383559246767383/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (778233370576405717111175532383559246767383/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3006 BracketBatch0187.bracket3007 (778233370576405717111175532383559246767383/5000000000000000000000000000000000000000) (1358252554616608804398312175067230324723/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3006 BracketBatch0187.bracket3007
  (778233370576405717111175532383559246767383/5000000000000000000000000000000000000000) (1358252554616608804398312175067230324723/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3006
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3007
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (48715169383634145492614712058597784370167/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48715169383634145492614712058597784370167/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (195469126508950771960944563086945408744541/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (195469126508950771960944563086945408744541/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (390329804043487353931403411321336546225209/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (390329804043487353931403411321336546225209/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0375.rows ScalarLogs0375.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0187.bracket3007 BracketBatch0188.bracket3008 (390329804043487353931403411321336546225209/2500000000000000000000000000000000000000) (3398006181595636774463078659223858118617/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0187.bracket3007 BracketBatch0188.bracket3008
  (390329804043487353931403411321336546225209/2500000000000000000000000000000000000000) (3398006181595636774463078659223858118617/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3007
