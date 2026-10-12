module

public import DedekindZetaZeroFree.Theta.Digits.AdelicPhases

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField IsDedekindDomain
open scoped Classical BigOperators NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem rational_residue_approx (p : KPFinitePlace F) (a : Fˣ)
    (ha : p.valuation F (a : F) ≤ 1) :
    ∃ r : 𝓞 F, p.valuation F ((r : F) - (a : F)) < 1 ∧
      Ideal.Quotient.mk p.asIdeal r = ThetaBranch.unitResidue p a := by
  obtain ⟨r, hr⟩ := p.exists_valuation_sub_lt_of_integer ha (1 : (WithZero (Multiplicative ℤ))ˣ)
  change p.valuation F ((r : F) - (a : F)) < 1 at hr
  refine ⟨r, hr, ?_⟩
  by_cases horder : ThetaBranch.order p a = 0
  · have hs : ThetaBranch.IsUnitResidue p a (ThetaBranch.unitResidue p a) := by
      simpa only [ThetaBranch.unitResidue, dif_pos horder] using
        (ThetaBranch.existsUnique_unitResidue p a horder).exists.choose_spec
    obtain ⟨b, c, hb, hc, he, ht⟩ := hs
    have hcval : p.valuation F (c : F) = 1 := p.valuation_eq_one_iff_notMem.mpr hc
    have hmul : p.valuation F ((c : F) * ((r : F) - (a : F))) < 1 := by
      rw [map_mul, hcval, one_mul]
      exact hr
    have he' : (c : F) * ((r : F) - (a : F)) = ((c * r - b : 𝓞 F) : F) := by
      rw [he]
      have hc0 : (c : F) ≠ 0 := by
        exact_mod_cast (fun h => hc (h ▸ p.asIdeal.zero_mem) : c ≠ 0)
      push_cast
      field_simp
    rw [he'] at hmul
    have hmem : c * r - b ∈ p.asIdeal := (p.valuation_lt_one_iff_mem (K := F) (c * r - b)).mp hmul
    have hred : Ideal.Quotient.mk p.asIdeal c * Ideal.Quotient.mk p.asIdeal r =
        Ideal.Quotient.mk p.asIdeal b := by
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa only [map_sub, map_mul, sub_eq_zero] using hh
    rw [ht]
    exact (eq_div_iff (fun h => hc (Ideal.Quotient.eq_zero_iff_mem.mp h))).mpr (by
      simpa only [mul_comm] using hred)
  · have hva : p.valuation F (a : F) ≠ 1 := by
      intro hv
      apply horder
      simp [ThetaBranch.order, hv]
    have hlt : p.valuation F (a : F) < 1 := lt_of_le_of_ne ha hva
    have hrv : p.valuation F (r : F) < 1 := by
      have hh := ValuationClass.map_add_le_max (p.valuation F) ((r : F) - (a : F)) (a : F)
      rw [sub_add_cancel] at hh
      exact hh.trans_lt (max_lt hr hlt)
    rw [ThetaBranch.unitResidue, dif_neg horder]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((p.valuation_lt_one_iff_mem (K := F) r).mp hrv)

theorem generator_valuation (p : ThetaBranch.ExteriorPrime R.A) :
    p.val.valuation F (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F) =
      WithZero.exp (-1 : ℤ) := by
  obtain ⟨r, hr, he⟩ := R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p)
  rw [he]
  have h := SIntegerLocalization.generator_valuation R.A.Sf
    (ThetaBranch.primeIdeal R.A p).val (ThetaBranch.primeIdeal R.A p).property.1
    r hr.1 hr.2 p.val p.property
  simpa [ThetaBranch.primeIdeal, idealPrimeExponent,
    UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible] using h

theorem valuation_le_exp_neg_one {z : WithZero (Multiplicative ℤ)} (hz : z < 1) :
    z ≤ WithZero.exp (-1 : ℤ) := by
  induction z using WithZero.expRecOn with
  | zero => simp
  | exp n =>
    simp only [WithZero.exp_lt_one_iff] at hz
    rw [WithZero.exp_le_exp]
    omega

theorem rational_local_phase (p : ThetaBranch.ExteriorPrime R.A) (a : Fˣ)
    (ha : p.val.valuation F (a : F) ≤ 1) (s : 𝓞 F) :
    (ResidueTrace.localTraceCharacter p.val
      (algebraMap F (p.val.adicCompletion F) (a : F) *
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) s) /
          algebraMap F (p.val.adicCompletion F)
            (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) : ℂ) =
      Characters.psi R p (ThetaBranch.unitResidue p.val a * Ideal.Quotient.mk p.val.asIdeal s) := by
  obtain ⟨r, hr, hred⟩ := rational_residue_approx p.val a ha
  let g : F := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  have hg : p.val.valuation F g = WithZero.exp (-1 : ℤ) := generator_valuation R p
  have hs : p.val.valuation F (s : F) ≤ 1 := p.val.valuation_le_one s
  have hi : algebraMap F (p.val.adicCompletion F) (((r : F) - (a : F)) * (s : F) / g) ∈
      p.val.adicCompletionIntegers F := by
    change Valued.v (algebraMap F (p.val.adicCompletion F) _) ≤ 1
    change Valued.v (((((r : F) - (a : F)) * (s : F) / g) : F) : p.val.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe, map_div₀, hg]
    apply (div_le_one₀ (by simp)).mpr
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left hs zero_le).trans (by
      simpa using valuation_le_exp_neg_one hr)
  have hc := CodifferentResidueSieve.localTraceCharacter_eq_one_of_integral p.val _ hi
  rw [← hred, ← map_mul, TraceHaarTransport.divided_negative_trace R p (r * s)]
  have he : algebraMap F (p.val.adicCompletion F) (a : F) *
      (-algebraMap (𝓞 F) (p.val.adicCompletion F) s) /
        algebraMap F (p.val.adicCompletion F) g =
      algebraMap F (p.val.adicCompletion F) (((r : F) - (a : F)) * (s : F) / g) +
        algebraMap F (p.val.adicCompletion F) (-(((r * s : 𝓞 F) : F) / g)) := by
    simp only [map_div₀, map_mul, map_sub, map_neg,
      ← IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F)]
    push_cast
    ring
  rw [he, AddChar.map_add_eq_mul, hc, one_mul]

theorem digitParameter_rational_phase (m : ThetaReflectionData.Row R.A) (a : Fˣ)
    (ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property,
      p.valuation F (a : F) ≤ 1)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ) =
      ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
        let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
        Characters.psi R ⟨p.val, hp⟩ (ThetaBranch.unitResidue p.val a * d p) := by
  rw [digitParameter_phase R]
  apply Finset.prod_congr rfl
  intro p _
  have h := rational_local_phase R ⟨p.val,
    ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩
    a (ha p.val p.property)
    ((ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)).lift p (d p))
  rw [ThetaDigitAverage.ResidueLifts.residue_lift] at h
  convert h using 2 <;> ring

end DedekindZetaZeroFree.DigitMasks

end
