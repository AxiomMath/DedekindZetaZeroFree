module

public import DedekindZetaZeroFree.CharacterSums.Gauss.SquarefreeCRT

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem norm_prod_eq (A : SArithmeticData F) (I : A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime A))
    (hI : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    A.exteriorNorm I = ∏ p ∈ P, idealNorm p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val := by
  unfold SArithmeticData.exteriorNorm idealNorm
  conv_lhs => rw [hI, map_prod]
  simp only [map_pow, Nat.cast_prod, Nat.cast_pow]

private theorem norm_inverse_prod (A : SArithmeticData F) (I : A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime A))
    (hI : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    (∏ p ∈ P, (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal I.val : ℤ))) =
      (A.exteriorNorm I : ℂ)⁻¹ := by
  simp only [zpow_neg, zpow_natCast]
  rw [Finset.prod_inv_distrib]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (norm_prod_eq A I P hI)
  push_cast at h
  exact congrArg Inv.inv h.symm

private theorem sqrt_inverse_prod (A : SArithmeticData F) (I : A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime A))
    (hI : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    (∏ p ∈ P, (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ ^ idealPrimeExponent p.val.asIdeal I.val) =
      (Real.sqrt (A.exteriorNorm I) : ℂ)⁻¹ := by
  simp only [inv_pow]
  rw [Finset.prod_inv_distrib]
  congr 1
  rw [norm_prod_eq A I P hI]
  have hreal : (∏ p ∈ P, Real.sqrt (idealNorm p.val.asIdeal) ^ idealPrimeExponent p.val.asIdeal I.val) =
      Real.sqrt (∏ p ∈ P, idealNorm p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) := by
    rw [Real.sqrt_prod _ (fun p hp => pow_nonneg (by unfold idealNorm; positivity) _)]
    apply Finset.prod_congr rfl
    intro p hp
    have hpow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : Real.sqrt (x ^ m) = Real.sqrt x ^ m := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx m), ih, pow_succ]
    exact (hpow _ (by unfold idealNorm; positivity) _).symm
  have h := congrArg (fun x : ℝ => (x : ℂ)) hreal
  push_cast at h
  exact h

theorem sphericalProduct (R : PrincipalMellin.ActualRecipe S η)
    (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hc : c.val.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal c.val.val)
    (hn : n.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal n.val) :
    let b := ∏ p ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
      (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
    (∏ p ∈ P, ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (MomentSources.Characters.psi R) p b) =
      R.probe.coefficients.gammaTwo c /
        ((Real.sqrt (R.A.exteriorNorm c.val) : ℂ) * (R.A.exteriorNorm n : ℂ)) := by
  let e := fun p : ThetaBranch.ExteriorPrime R.A => idealPrimeExponent p.val.asIdeal c.val.val
  let k := fun p : ThetaBranch.ExteriorPrime R.A => idealPrimeExponent p.val.asIdeal n.val
  let r := fun p : ThetaBranch.ExteriorPrime R.A =>
    Classical.choose (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))
  have he : ∀ p, e p = 0 ∨ e p = 1 := squarefree_exps R.A c
  have hr (p : ThetaBranch.ExteriorPrime R.A) :
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F) = (r p : F) :=
    (Classical.choose_spec (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))).2
  have hl (p : ThetaBranch.ExteriorPrime R.A) (hp : p ∈ P) :=
    sphericalFactor_generatorProduct R.A R.probe.allowed R.σ (MomentSources.Characters.psi R) P e k p hp (he p)
  simp_rw [generatorProduct_phase R.A R.probe.allowed R.σ P e k r hr] at hl
  dsimp only
  calc
    _ = ∏ p ∈ P, (idealNorm p.val.asIdeal : ℂ) ^ (-(k p : ℤ)) *
        (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ ^ e p *
        ThetaBranch.gaussTwo R.A R.σ (MomentSources.Characters.psi R) p ^ e p *
        (∏ q ∈ P.erase p, R.σ (R.A.sexticResidue (ThetaBranch.primeIdeal R.A p) (r q)) ^ (2 * e p * e q)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hl p hp
    _ = _ := by
      simp only [Finset.prod_mul_distrib]
      rw [norm_inverse_prod R.A n P hn, sqrt_inverse_prod R.A c.val P hc]
      have hg := gauss_finiteProduct R c P hc
      dsimp only at hg
      rw [hg]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical

end
