module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.RationalUnitCharacters

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_spec → reduction_spec
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_mul → reduction_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_pow → reduction_pow
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_one → reduction_one
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem order_mul (p : KPFinitePlace F) (x y : Fˣ) :
    ThetaBranch.order p (x * y) = ThetaBranch.order p x + ThetaBranch.order p y := by
  simp only [ThetaBranch.order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

theorem order_zpow (p : KPFinitePlace F) (x : Fˣ) (n : ℤ) :
    ThetaBranch.order p (x ^ n) = n * ThetaBranch.order p x := by
  simp only [ThetaBranch.order, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem order_inv (p : KPFinitePlace F) (x : Fˣ) :
    ThetaBranch.order p x⁻¹ = -ThetaBranch.order p x := by
  simpa using order_zpow p x (-1)

theorem order_neg (p : KPFinitePlace F) (x : Fˣ) :
    ThetaBranch.order p (-x) = ThetaBranch.order p x := by
  simp [ThetaBranch.order]

theorem generator_order (p : ThetaBranch.ExteriorPrime R.A) :
    ThetaBranch.order p.val (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)) = 1 := by
  rw [ThetaBranch.generator_order]
  simp [ThetaBranch.primeIdeal, idealPrimeExponent,
    UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]

theorem reduction_inv (p : KPFinitePlace F) (x : Fˣ) (hx : ThetaBranch.order p x = 0) :
    ThetaBranch.unitResidue p x⁻¹ = (ThetaBranch.unitResidue p x)⁻¹ := by
  have hi : ThetaBranch.order p x⁻¹ = 0 := by rw [order_inv, hx, neg_zero]
  have hm := reduction_mul p x x⁻¹ hx hi
  rw [mul_inv_cancel, reduction_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

theorem reduction_neg (p : KPFinitePlace F) (x : Fˣ) (hx : ThetaBranch.order p x = 0) :
    ThetaBranch.unitResidue p (-x) = -ThetaBranch.unitResidue p x := by
  have hn : ThetaBranch.order p (-x) = 0 := by rw [order_neg, hx]
  apply (ThetaBranch.existsUnique_unitResidue p (-x) hn).unique (reduction_spec p (-x) hn)
  obtain ⟨a,b,ha,hb,he,hr⟩ := reduction_spec p x hx
  refine ⟨-a,b, ?_,hb, ?_, ?_⟩
  · simpa using ha
  · simp only [Units.val_neg, map_neg, he, neg_div]
  · rw [map_neg, neg_div, hr]

theorem reduction_integral (p : KPFinitePlace F) (t : 𝓞 F) (ht : t ∉ p.asIdeal) :
    ThetaBranch.unitResidue p (Units.mk0 (t : F) (by
      exact_mod_cast (fun h => ht (h ▸ p.asIdeal.zero_mem) : t ≠ 0))) = Ideal.Quotient.mk p.asIdeal t := by
  let x := Units.mk0 (t : F) (show (t : F) ≠ 0 by
    exact_mod_cast (fun h => ht (h ▸ p.asIdeal.zero_mem) : t ≠ 0))
  have hx : ThetaBranch.order p x = 0 := by
    simp [ThetaBranch.order, x, p.valuation_eq_one_iff_notMem.mpr ht]
  apply (ThetaBranch.existsUnique_unitResidue p x hx).unique (reduction_spec p x hx)
  exact ⟨t,1,ht,p.isPrime.one_notMem,by simp [x],by simp⟩

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
