module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace DedekindZetaZeroFree.DifferentMass

noncomputable section

def exponent (F : Type*) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : ℕ :=
  multiplicity v.asIdeal (differentIdeal ℤ (NumberField.RingOfIntegers F))

def halfNormMass (F : Type*) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : ℝ :=
  1 / Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ exponent F v)

theorem differentIdeal_ne_bot (F : Type*) [Field F] [NumberField F] :
    differentIdeal ℤ (NumberField.RingOfIntegers F) ≠ ⊥ := by
  exact _root_.differentIdeal_ne_bot

theorem one_lt_absNorm (F : Type*) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    1 < Ideal.absNorm v.asIdeal := by
  exact NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v

theorem exponent_finite_support (F : Type*) [Field F] [NumberField F] :
    Set.Finite {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) |
      exponent F v ≠ 0} := by
  refine (Ideal.finite_factors (differentIdeal_ne_bot F)).subset ?_
  intro v hv
  exact dvd_of_multiplicity_pos (Nat.pos_of_ne_zero hv)

end

end DedekindZetaZeroFree.DifferentMass

section

namespace DedekindZetaZeroFree.DifferentMass

noncomputable section

theorem halfNormMass_eq_one (F : Type*) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hv : exponent F v = 0) : halfNormMass F v = 1 := by
  simp [halfNormMass, hv]

theorem finprod_halfNormMass_eq_natAbs_discr (F : Type*) [Field F] [NumberField F] :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      halfNormMass F v) = 1 / Real.sqrt ((NumberField.discr F).natAbs : ℝ) := by
  classical
  let s := (exponent_finite_support F).toFinset
  have hs (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (hv : exponent F v ≠ 0) : v ∈ s := by
    exact (exponent_finite_support F).mem_toFinset.mpr hv
  have hfactor : (∏ v ∈ s, v.asIdeal ^ exponent F v) =
      differentIdeal ℤ (NumberField.RingOfIntegers F) := by
    rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity (differentIdeal_ne_bot F)]
    symm
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    apply hs
    intro h
    exact hv (by simp [exponent] at h ⊢; simp [h])
  have hnorm : (∏ v ∈ s, (Ideal.absNorm v.asIdeal : ℝ) ^ exponent F v) =
      ((NumberField.discr F).natAbs : ℝ) := by
    have h := congrArg (fun I => (Ideal.absNorm I : ℝ)) hfactor
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow,
      NumberField.absNorm_differentIdeal F (NumberField.RingOfIntegers F)] using h
  rw [finprod_eq_prod_of_mulSupport_subset (halfNormMass F) (s := s) (by
    intro v hv
    exact hs v (fun h => hv (halfNormMass_eq_one F v h)))]
  simp only [halfNormMass, Finset.prod_div_distrib, Finset.prod_const_one]
  rw [← Real.sqrt_prod s (fun v _ => pow_nonneg (Nat.cast_nonneg _) _), hnorm]

theorem finprod_halfNormMass_eq_abs_discr (F : Type*) [Field F] [NumberField F] :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      halfNormMass F v) = 1 / Real.sqrt |(NumberField.discr F : ℝ)| := by
  rw [finprod_halfNormMass_eq_natAbs_discr]
  congr 2
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

end

end DedekindZetaZeroFree.DifferentMass

end
