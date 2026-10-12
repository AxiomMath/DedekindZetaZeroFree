module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField ValuativeRel IsDedekindDomain
open scoped NumberField Classical
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency true
local notation "ℤᵐ⁰" => WithZero (Multiplicative ℤ)
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_completion_generator_valuation (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    Valued.v (exteriorCompletionGenerator R p : p.val.adicCompletion F) =
      WithZero.exp (-1 : ℤ) := by
  obtain ⟨r, hr, he⟩ := R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p)
  have hv := SIntegerLocalization.generator_completion_valuation R.A.Sf
    (ThetaBranch.primeIdeal R.A p).val (ThetaBranch.primeIdeal R.A p).property.1
    r hr.1 hr.2 _ he p.val p.property
  simpa [ThetaBranch.primeIdeal, idealPrimeExponent,
    UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible] using hv

theorem exterior_trace_detects_nonintegral_diagonal (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (y : (p.val.adicCompletion F)ˣ)
    (hy : (y : p.val.adicCompletion F) ∉ p.val.adicCompletionIntegers F) :
    ∃ o : p.val.adicCompletionIntegers F,
      ResidueTrace.localTraceCharacter p.val ((y : p.val.adicCompletion F) * o.val) ≠ 1 := by
  by_contra h
  push Not at h
  exact hy ((R.traceBad p.val p.property _).mp h)

private theorem residueChar_mem (q : KPFinitePlace F) (n : ℕ)
    (hn : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = n) :
    (n : 𝓞 F) ∈ q.asIdeal := by
  let ν : Valuation (KPTameCompact.K F q) ℤᵐ⁰ := Valued.v
  letI : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hz : (n : KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 0 := by
    rw [← hn]
    exact CharP.cast_eq_zero _ (ringChar _)
  have hp : (n : KPTameCompact.O F q) ∈ KPTameCompact.p F q :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hz)
  have hnu : ¬ IsUnit (n : KPTameCompact.O F q) :=
    (IsLocalRing.mem_maximalIdeal _).mp hp
  have hlt := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hnu
  have ht : ν (n : KPTameCompact.K F q) < 1 := by
    rw [← Valuation.vlt_one_iff, Valuation.vlt_one_iff (ValuativeRel.valuation _)]
    exact hlt
  have he : ν (n : KPTameCompact.K F q) =
      q.valuation F (algebraMap (𝓞 F) F (n : 𝓞 F)) := by
    simpa only [map_natCast] using q.valuedAdicCompletion_eq_valuation (K := F) (n : 𝓞 F)
  rw [he, q.valuation_lt_one_iff_mem] at ht
  exact ht

theorem exterior_prime_not_bad (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) : ¬ KPAdelicCoverRestrictedProduct.Bad F p.val := by
  intro h
  apply p.property
  apply R.A.above_six
  rcases h with h | h
  · have hm := residueChar_mem p.val 2 h
    have hh := p.val.asIdeal.mul_mem_right (3 : 𝓞 F) hm
    norm_num at hh ⊢
    exact hh
  · have hm := residueChar_mem p.val 3 h
    have hh := p.val.asIdeal.mul_mem_left (2 : 𝓞 F) hm
    norm_num at hh ⊢
    exact hh

theorem exterior_integral_root_mem_compact (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (o : p.val.adicCompletionIntegers F) :
    KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  letI : (Valued.v : Valuation (p.val.adicCompletion F) ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation _
  have hint : o.val ∈ KPTameCompact.O F p.val :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation (p.val.adicCompletion F))
      (Valued.v : Valuation (p.val.adicCompletion F) ℤᵐ⁰)).le_one_iff_le_one.mpr o.property
  let t : KPTameCompact.O F p.val := ⟨o.val, hint⟩
  have hg := exterior_prime_not_bad R p
  have ht : ringChar (KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) ≠ 3 :=
    fun h => hg (Or.inr h)
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hg]
  refine ⟨KPStandardLocalRootLifts.integralN F p.val t, ?_⟩
  exact (KPStandardLocalRootLifts.N_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val ht t).symm

theorem exterior_whittaker_value_eq_zero_of_neg (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (hW : ExteriorWhittakerEquivariance R C)
    (p : ThetaBranch.ExteriorPrime R.A) (e : ℤ) (he : e < 0) :
    exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ e) = 0 := by
  let y := exteriorCompletionGenerator R p ^ e
  have hyval : Valued.v (y : p.val.adicCompletion F) = WithZero.exp (-e) := by
    have hz : Valued.v (y : p.val.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr y.ne_zero
    rw [← WithZero.exp_log hz]
    congr 1
    dsimp [y]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow,
      exterior_completion_generator_valuation, WithZero.log_exp]
    simp
  have hy : (y : p.val.adicCompletion F) ∉ p.val.adicCompletionIntegers F := by
    intro hi
    have hh : Valued.v (y : p.val.adicCompletion F) ≤ 1 := hi
    rw [hyval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hh
    omega
  obtain ⟨o, ho⟩ := exterior_trace_detects_nonintegral_diagonal R p y hy
  let z : p.val.adicCompletion F := y.val * o.val
  have hzdiv : z / y.val = o.val := by
    dsimp [z]
    exact mul_div_cancel_left₀ o.val y.ne_zero
  let ρ := exteriorImageAction R C p
  let b := C.factorization.references (Sum.inr p.val)
  let a := KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y
  let n := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z
  let n₀ := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val
  have hconj : n * a = a * n₀ := by
    dsimp [n, a, n₀]
    rw [KPCorrectedBruhatLifts.quotient_upper_diagonal, hzdiv]
  have hs : ρ n₀ b = b := (C.factorization.spherical_reference p.val p.property).2
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val)
    (exterior_integral_root_mem_compact R p o)
  have hfix : ρ n (ρ a b) = ρ a b := by
    calc
      ρ n (ρ a b) = ρ (n * a) b := (LinearMap.congr_fun (ρ.map_mul n a) b).symm
      _ = ρ (a * n₀) b := congrArg (fun g => ρ g b) hconj
      _ = ρ a (ρ n₀ b) := LinearMap.congr_fun (ρ.map_mul a n₀) b
      _ = ρ a b := congrArg (ρ a) hs
  have hphase : (ResidueTrace.localTraceCharacter p.val z : ℂ) ≠ 1 := by
    intro hh
    apply ho
    exact Circle.coe_injective (by simpa using hh)
  have hw := hW p z (ρ a b)
  change C.factorization.ell (Sum.inr p.val) (ρ n (ρ a b)) =
    (ResidueTrace.localTraceCharacter p.val z : ℂ) *
      C.factorization.ell (Sum.inr p.val) (ρ a b) at hw
  rw [hfix] at hw
  have hv : C.factorization.ell (Sum.inr p.val) (ρ a b) = exteriorWhittakerValue R C p y := by
    unfold exteriorWhittakerValue
    rw [exterior_diagonal_eq_standard_lift]
  rw [hv] at hw
  have hzval : ((ResidueTrace.localTraceCharacter p.val z : ℂ) - 1) *
      exteriorWhittakerValue R C p y = 0 := by
    rw [sub_mul, one_mul, ← hw, sub_self]
  exact (mul_eq_zero.mp hzval).resolve_left (sub_ne_zero.mpr hphase)

end DedekindZetaZeroFree.ThetaExpansion

end
