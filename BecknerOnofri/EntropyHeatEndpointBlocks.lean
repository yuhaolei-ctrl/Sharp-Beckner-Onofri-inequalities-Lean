import BecknerOnofri.EntropyHeatIntegerPanelCertificate

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

structure CheckedExp where
  value : Entry
  valid : value.Valid

def checkedExpAt (c : CheckedChunk) (i : Fin c.entries.length) : CheckedExp :=
  ⟨c.entries[i], c.valid i⟩

inductive Endpoint where
  | small (data : SmallEndpoint) (hd : data.directExp.Valid) (hm : data.modularExp.Valid)
  | large (data : LargeEndpoint) (h1 : data.e1.Valid) (h4 : data.e4.Valid)
      (h9 : data.e9.Valid) (h16 : data.e16.Valid) (h25 : data.e25.Valid) (h11 : data.e11.Valid)

def Endpoint.ofSmall (s U : ℚ) (e q : CheckedExp) : Endpoint :=
  .small ⟨s, U, e.value, q.value⟩ e.valid q.valid

def Endpoint.ofLarge (s U : ℚ) (e1 e4 e9 e16 e25 e11 : CheckedExp) : Endpoint :=
  .large ⟨s, U, e1.value, e4.value, e9.value, e16.value, e25.value, e11.value⟩
    e1.valid e4.valid e9.valid e16.valid e25.valid e11.valid

def Endpoint.point : Endpoint → ℚ
  | .small p _ _ => p.point
  | .large p _ _ _ _ _ _ => p.point

def Endpoint.upper : Endpoint → ℚ
  | .small p _ _ => p.upper
  | .large p _ _ _ _ _ _ => p.upper

def Endpoint.check : Endpoint → Bool
  | .small p _ _ => p.integerCheck
  | .large p _ _ _ _ _ _ => p.integerCheck

theorem Endpoint.sound (e : Endpoint) (h : e.check = true) :
    heatComplement (e.point : ℝ) ≤ (e.upper : ℝ) := by
  cases e with
  | small p hd hm => exact p.sound_integer h hd hm
  | large p h1 h4 h9 h16 h25 h11 => exact p.sound_integer h h1 h4 h9 h16 h25 h11

structure CheckedEndpoints where
  entries : List Endpoint
  accepted : entries.all Endpoint.check = true

theorem CheckedEndpoints.sound (c : CheckedEndpoints) (e : Endpoint) (he : e ∈ c.entries) :
    heatComplement (e.point : ℝ) ≤ (e.upper : ℝ) :=
  e.sound (List.all_eq_true.mp c.accepted e he)

#print axioms CheckedEndpoints.sound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
