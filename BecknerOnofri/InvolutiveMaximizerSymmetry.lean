module

public import BecknerOnofri.LatticeMaximizerSupport
public import BecknerOnofri.GinibreStrictSupermodularity

@[expose] public section

/-! An actual maximizer is fixed by every verified involutive coefficient
symmetry. All support, maximum/minimum, and strict-covariance arguments are
proved for the genuine Sobolev functional. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment
open GinibreCovariance

theorem involutive_maximizer_coefficients {d : ℕ} (hd : 0<d)
    {a b : Frequency d → ℝ} (ha : Domain a) (hb : Domain b)
    (e : Frequency d ≃+ Frequency d) (he : Function.Involutive e)
    (hba : ∀ k,b k=a (e k)) {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a))
    (hvalue : functional A (toPotential b)=functional A (toPotential a)) : a=b := by
  have hmaxb : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential b) := by
    intro v hv
    rw [hvalue]
    exact hmax v hv
  have hlattice := lattice_maximizers ha hb A (functional A (toPotential a)) hmax rfl hvalue
  have hmaxsup : ∀ v : TorusL2 d,Admissible v → functional A v≤
      functional A (toPotential (fun k => max (a k) (b k))) := by
    intro v hv
    rw [hlattice.1]
    exact hmax v hv
  let L := maximizerSupport hd ha hA hmax
  let M := maximizerSupport hd hb hA hmaxb
  let N := maximizerSupport hd (ha.max hb) hA hmaxsup
  have hN (k : Frequency d) : k∈N ↔ k∈L ∨ k∈M := by
    change (k=0 ∨ 0<max (a k) (b k))↔(k=0 ∨ 0<a k) ∨ (k=0 ∨ 0<b k)
    rw [lt_max_iff]
    tauto
  have hM (k : Frequency d) : k∈M ↔ e k∈L := by
    change (k=0 ∨ 0<b k)↔(e k=0 ∨ 0<a (e k))
    rw [hba,e.map_eq_zero_iff]
  have heq (k : Frequency d) : k∈L ↔ k∈M := by
    rcases subgroup_union_comparable L M N hN with hLM | hML
    · constructor
      · intro hk
        exact hLM hk
      · intro hk
        have h := (hM (e k)).mp (hLM ((hM k).mp hk))
        rw [he k] at h
        exact h
    · constructor
      · intro hk
        have h := hML ((hM (e k)).mpr (by rw [he k]; exact hk))
        exact (hM k).mpr h
      · intro hk
        exact hML hk
  have hbe (k : Frequency d) : b (e k)=a k := by rw [hba,he]
  have hnot (r : Frequency d) : ¬b r<a r := by
    intro hpr
    let s := e r
    have hqs : a s<b s := by simpa only [s,hbe,← hba] using hpr
    have hr : r≠0 := by intro hz; simpa [hz,ha.zero,hb.zero] using hpr
    have hs : s≠0 := by
      intro hz
      exact hr (e.injective (hz.trans e.map_zero.symm))
    have hrs : r≠s := by intro h; have := hqs; rw [← h] at this; linarith
    have hra : 0<a r := (hb.nonneg r).trans_lt hpr
    have hrL : r∈L := Or.inr hra
    have hsL : s∈L := (hM r).mp ((heq r).mp hrL)
    have hdL : r-s∈L := L.sub_mem hrL hsL
    have hdM : r-s∈M := (heq (r-s)).mp hdL
    have hd0 : r-s≠0 := sub_ne_zero.mpr hrs
    have had : 0<a (r-s) := Or.resolve_left hdL hd0
    have hbd : 0<b (r-s) := Or.resolve_left hdM hd0
    have hstrict := functional_strict_supermodular ha hb A r s hr hs hrs hpr hqs (lt_min had hbd)
    rw [hlattice.1,hlattice.2,hvalue] at hstrict
    linarith
  funext k
  apply le_antisymm
  · exact le_of_not_gt (hnot k)
  · have hh := le_of_not_gt (hnot (e k))
    simpa only [hbe,← hba] using hh

#print axioms involutive_maximizer_coefficients
end BecknerOnofri.HighDim.CosineCoefficientLattice
