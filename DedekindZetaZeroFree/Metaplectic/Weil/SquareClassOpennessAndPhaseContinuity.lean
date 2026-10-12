module

public import DedekindZetaZeroFree.Metaplectic.Weil.SquareScalingAndPhaseNorms
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing

@[expose] public section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F]

def finiteSquareSubgroup (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (v.adicCompletion F)ˣ := (powMonoidHom 2).range

open Polynomial in
private theorem finite_square_hensel (v : HeightOneSpectrum (𝓞 F))
    (z : (v.adicCompletion F)ˣ)
    (hz : Valued.v ((z : v.adicCompletion F)-1) < Valued.v (2 : v.adicCompletion F)^2) :
    ∃ t : (v.adicCompletion F)ˣ, t^2 = z := by
  let K := v.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let O := ν.valuationSubring
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : HenselianRing O m :=
    (LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν).henselianRing
  have h4 : ν (4 : K) = ν (2 : K)^2 := by
    rw [show (4 : K) = 2^2 by norm_num, map_pow]
  have h4n : ν (4 : K) ≠ 0 := (ν.map_eq_zero_iff).not.mpr (by norm_num)
  have hc : ν (((z : K)-1)/4) < 1 := by
    rw [map_div₀, div_lt_one₀ (pos_iff_ne_zero.mpr h4n), h4]
    exact hz
  let c : O := ⟨((z : K)-1)/4, hc.le⟩
  have hcm : c ∈ m := (Valuation.mem_maximalIdeal_iff K ν).mpr hc
  let P : O[X] := X^2 - X - C c
  have hm : P.Monic := by
    rw [show P = X^2 - (X + C c) by dsimp [P]; ring]
    apply monic_X_pow_sub
    compute_degree
    norm_num
  have he : P.eval 1 ∈ m := by
    simpa [P] using m.neg_mem hcm
  have hd : IsUnit ((Ideal.Quotient.mk m) (P.derivative.eval 1)) := by
    have h : P.derivative.eval 1 = 1 := by simp [P]
    rw [h, map_one]
    exact isUnit_one
  obtain ⟨b, hb, _⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hb' : (b : K)^2 - (b : K) - ((z : K)-1)/4 = 0 := by
    have h : b^2 - b - c = 0 := by simpa [Polynomial.IsRoot, P] using hb
    exact congrArg (fun x : O => (x : K)) h
  have ht : (2*(b : K)-1)^2 = (z : K) := by
    linear_combination 4*hb'
  have htn : 2*(b : K)-1 ≠ 0 := by
    intro h
    exact z.ne_zero (by simpa [h] using ht.symm)
  exact ⟨Units.mk0 _ htn, Units.ext (by simpa using ht)⟩

theorem finiteSquareSubgroup_isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (finiteSquareSubgroup v : Set (v.adicCompletion F)ˣ) := by
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have h : ∀ᶠ z : (v.adicCompletion F)ˣ in nhds 1,
      Valued.v ((z : v.adicCompletion F)-1) < Valued.v (2 : v.adicCompletion F)^2 := by
    have h0 : Valued.v (2 : v.adicCompletion F)^2 ≠ 0 := by
      exact pow_ne_zero _ ((Valued.v.map_eq_zero_iff).not.mpr (by norm_num : (2 : v.adicCompletion F) ≠ 0))
    have hball : {x : v.adicCompletion F | Valued.v x < Valued.v (2 : v.adicCompletion F)^2} ∈ nhds 0 := by
      apply Valued.mem_nhds_zero.mpr
      refine ⟨Units.mk0 (Valued.v.restrict (2 : v.adicCompletion F) ^ 2) ?_, ?_⟩
      · simpa using h0
      · intro x hx
        simpa only [Units.val_mk0, ← map_pow, Valuation.restrict_lt_iff] using hx
    have ht : Filter.Tendsto (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)-1)
        (nhds 1) (nhds 0) := by
      have hc : Continuous (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)-1) :=
        Units.continuous_val.sub continuous_const
      simpa only [ContinuousAt, Units.val_one, sub_self] using hc.continuousAt (x := 1)
    exact ht.eventually hball
  apply Filter.mem_of_superset h
  intro z hz
  exact finite_square_hensel v z hz

end
end DedekindZetaZeroFree
