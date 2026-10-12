module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals
public import DedekindZetaZeroFree.Arithmetic.LocalFields.StandardResidueTraceCharacter

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField ValuativeRel IsDedekindDomain
open scoped NumberField Classical Valued
local notation "ℤᵐ⁰" => WithZero (Multiplicative ℤ)
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_rational_completion_decomposition (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    ∃ (u : (p.val.adicCompletion F)ˣ) (t : 𝓞 F),
      Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x =
        exteriorCompletionGenerator R p ^ ThetaBranch.order p.val x * u ∧
      ‖(u : p.val.adicCompletion F) - algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1 ∧
      valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1 ∧
      Ideal.Quotient.mk p.val.asIdeal t =
        ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) := by
  let y := ThetaBranch.localUnit R.A R.probe.allowed p x
  let u := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom y
  have hy : ThetaBranch.order p.val y = 0 := ThetaBranch.localUnit_order R.A R.probe.allowed p x
  have hv : p.val.valuation F (y : F) = 1 := by
    have hz : p.val.valuation F (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
    have hl : WithZero.log (p.val.valuation F (y : F)) = 0 := by
      simpa only [ThetaBranch.order, neg_eq_zero] using hy
    rw [← WithZero.exp_log hz, hl, WithZero.exp_zero]
  have huv : Valued.v (u : p.val.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (p.val.adicCompletion F) (y : F)) = 1
    exact (p.val.valuedAdicCompletion_eq_valuation' (y : F)).trans hv
  have hu : valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1 := by
    letI : (Valued.v : Valuation (p.val.adicCompletion F) ℤᵐ⁰).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ((ValuativeRel.isEquiv (Valued.v : Valuation (p.val.adicCompletion F) ℤᵐ⁰)
      (valuation (p.val.adicCompletion F))).eq_one_iff_eq_one).mp huv
  let ui : p.val.adicCompletionIntegers F := ⟨u.val, huv.le⟩
  let red := PrincipalMellinSource.ProfileCore.FixedSupport.standardReduction p.val
  let eqv := PrincipalMellinSource.ProfileCore.FixedSupport.standardResidueFieldEquiv p.val
  have hred (a : 𝓞 F) : eqv (red ⟨algebraMap (𝓞 F) (p.val.adicCompletion F) a,
      p.val.coe_mem_adicCompletionIntegers (K := F) a⟩) = Ideal.Quotient.mk p.val.asIdeal a := by
    apply eqv.symm.injective
    rw [RingEquiv.symm_apply_apply]
    rfl
  have hres : eqv (red ui) = ThetaBranch.unitResidue p.val y := by
    have hs : ThetaBranch.IsUnitResidue p.val y (ThetaBranch.unitResidue p.val y) := by
      simpa only [ThetaBranch.unitResidue, dif_pos hy] using
        (ThetaBranch.existsUnique_unitResidue p.val y hy).exists.choose_spec
    obtain ⟨a, b, ha, hb, he, hr⟩ := hs
    let ai : p.val.adicCompletionIntegers F :=
      ⟨algebraMap (𝓞 F) (p.val.adicCompletion F) a, p.val.coe_mem_adicCompletionIntegers (K := F) a⟩
    let bi : p.val.adicCompletionIntegers F :=
      ⟨algebraMap (𝓞 F) (p.val.adicCompletion F) b, p.val.coe_mem_adicCompletionIntegers (K := F) b⟩
    have hmul : ui * bi = ai := by
      apply Subtype.ext
      change algebraMap F (p.val.adicCompletion F) (y : F) * algebraMap F _ (b : F) = algebraMap F _ (a : F)
      rw [← map_mul, he, div_mul_cancel₀]
      intro hh
      have hb0 : b = 0 := by exact_mod_cast hh
      exact hb (hb0 ▸ p.val.asIdeal.zero_mem)
    have hh := congrArg (fun z : p.val.adicCompletionIntegers F => eqv (red z)) hmul
    simp only [map_mul] at hh
    rw [hred a, hred b] at hh
    rw [hr]
    exact (eq_div_iff (fun hz => hb (Ideal.Quotient.eq_zero_iff_mem.mp hz))).mpr hh
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ThetaBranch.unitResidue p.val y)
  let ti : p.val.adicCompletionIntegers F :=
    ⟨algebraMap (𝓞 F) (p.val.adicCompletion F) t, p.val.coe_mem_adicCompletionIntegers (K := F) t⟩
  have hr : red ui = red ti := eqv.injective (hres.trans ((hred t).trans ht).symm)
  have hm : ui - ti ∈ IsLocalRing.maximalIdeal (p.val.adicCompletionIntegers F) := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    change red (ui - ti) = 0
    rw [map_sub, hr, sub_self]
  have hlt : ‖(u : p.val.adicCompletion F) - algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1 := by
    apply Valued.toNormedField.norm_lt_one_iff.mpr
    exact (Valuation.mem_maximalIdeal_iff (p.val.adicCompletion F)
      (Valued.v : Valuation (p.val.adicCompletion F) ℤᵐ⁰) (a := ui - ti)).mp hm
  refine ⟨u, t, ?_, hlt, hu, ht⟩
  change Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x =
    Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)) ^ ThetaBranch.order p.val x *
    Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom y
  rw [← map_zpow, ← map_mul]
  congr 1
  dsimp [y, ThetaBranch.localUnit]
  exact (mul_div_cancel _ _).symm

end DedekindZetaZeroFree.ThetaExpansion

end
