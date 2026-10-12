module

public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Global.FiniteSetEnlargement

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators Topology
open Filter IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorFactorLimit
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

 def primeEquiv : HeightOneSpectrum (𝓞 F) ≃ ExteriorIdealEuler.PrimeIndex (⊤ : Ideal (𝓞 F)) where
  toFun q := ⟨⟨q.asIdeal,q.ne_bot,by simp⟩,q.prime⟩
  invFun q := HeightOneSpectrum.ofPrime q.property
  left_inv q := rfl
  right_inv q := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem global_inverse_euler (z : ℂ) (hz : 1 < z.re) :
    HasProd (fun q : HeightOneSpectrum (𝓞 F) => 1 - (Ideal.absNorm q.asIdeal : ℂ)^(-z))
      (GlobalZetaNormalizer.zeta  F ζ hζ z)⁻¹ ∧
    GlobalZetaNormalizer.zeta  F ζ hζ z ≠ 0 := by
  have h := ExteriorIdealEuler.exterior_ideal_euler
    (fun _ : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => (1 : ℂ))
    (ExteriorIdealEuler.constant_one_isCoefficient _) z hz
  have heq : (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)),
      ExteriorIdealEuler.summand (fun _ => (1 : ℂ)) z I) = GlobalZetaNormalizer.zeta  F ζ hζ z := by
    rw [← (GlobalZetaNormalizer.actual_principal_continuation  F ζ hζ).2.2.2.2.2.2.2 z hz |>.tsum_eq]
    simp only [ExteriorIdealEuler.summand,one_mul]
    apply tsum_subtype_eq_of_support_subset
      (f := fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℂ)^(-z))
      (s := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤})
    intro I hI
    refine ⟨?_,by simp⟩
    intro hbot
    subst I
    have hz0 : -z ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (by linarith))
    simp [Ideal.absNorm_bot, Complex.zero_cpow hz0] at hI
  rw [heq] at h
  have hp := (primeEquiv F).hasProd_iff.mpr h.2.2.2
  refine ⟨?_,h.2.2.1⟩
  apply hp.congr
  intro q
  simp only [Function.comp_apply, primeEquiv, Equiv.coe_fn_mk,
    ExteriorIdealEuler.primeTerm, ExteriorIdealEuler.summand, one_mul]

private theorem local_euler_nonzero (z : ℂ) (hz : 1 < z.re)
    (q : HeightOneSpectrum (𝓞 F)) : 1 - (Ideal.absNorm q.asIdeal : ℂ)^(-z) ≠ 0 := by
  have hq : (1 : ℝ) < Ideal.absNorm q.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm q
  have hn : ‖(Ideal.absNorm q.asIdeal : ℂ)^(-z)‖ < 1 := by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simp only [Complex.neg_re]; linarith)
  intro h
  have he := (sub_eq_zero.mp h).symm
  exact (lt_irrefl (1 : ℝ)) (by simpa only [he,norm_one] using hn)

private theorem exterior_inverse_euler
    (E : Finset (HeightOneSpectrum (𝓞 F))) (z : ℂ) (hz : 1 < z.re) :
    HasProd (fun q : HeightOneSpectrum (𝓞 F) => if q ∈ E then 1 else
      1 - (Ideal.absNorm q.asIdeal : ℂ)^(-z))
      (GlobalZetaNormalizer.exteriorZeta  F ζ hζ E z)⁻¹ ∧
    GlobalZetaNormalizer.exteriorZeta  F ζ hζ E z ≠ 0 := by
  have h := global_inverse_euler F ζ hζ  z hz
  have he := h.1.congr_cofinite₀ (s := E)
    (g := fun q => if q ∈ E then 1 else 1 - (Ideal.absNorm q.asIdeal : ℂ)^(-z))
    (fun q _ => local_euler_nonzero F z hz q) (fun q hq => by simp [hq])
  have hd : PositiveZetaResidue.exteriorEulerFactor F E z ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => local_euler_nonzero F z hz q)
  have hone : (∏ q ∈ E, if q ∈ E then (1 : ℂ) else
      1 - (Ideal.absNorm q.asIdeal : ℂ)^(-z)) = 1 :=
    Finset.prod_eq_one (fun q hq => by simp [hq])
  rw [hone] at he
  refine ⟨?_,mul_ne_zero h.2 hd⟩
  convert he using 1
  simp [GlobalZetaNormalizer.exteriorZeta,PositiveZetaResidue.exteriorEulerFactor,
    div_eq_mul_inv, mul_comm]

theorem exterior_goodFactor_hasProd
    (E : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) (hs : (1 : ℝ)/3 < s.re) :
    HasProd (fun q : HeightOneSpectrum (𝓞 F) => if q ∈ E then 1 else
      KPGlobalFiniteSIntertwiner.goodFactor F q s)
      (KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E s) := by
  have h1 := exterior_inverse_euler F ζ hζ  E (1+6*s) (by simp only [Complex.add_re,Complex.mul_re]; norm_num; linarith)
  have h2 := exterior_inverse_euler F ζ hζ  E (2+6*s) (by simp only [Complex.add_re,Complex.mul_re]; norm_num; linarith)
  have hp := h2.1.div₀ h1.1 (inv_ne_zero h1.2)
  convert hp using 1
  · funext q
    by_cases hq : q ∈ E
    · simp [hq]
    · simp only [hq,ite_false,KPGlobalFiniteSIntertwiner.goodFactor,
        KPGlobalGoodEulerFactor.sphericalCoefficient,Complex.ofReal_one,one_mul]
      have he (a : ℂ) : (Ideal.absNorm q.asIdeal : ℂ)^(-(a+6*s)) =
          Complex.exp ((-a-6*s)*(Real.log (KPGlobalFiniteSIntertwiner.residueSize F q) : ℂ)) := by
        have hn : (Ideal.absNorm q.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm q)))
        rw [Complex.cpow_def_of_ne_zero hn,← Complex.ofReal_natCast,
          ← Complex.ofReal_log (by positivity)]
        simp only [KPGlobalFiniteSIntertwiner.residueSize]
        congr 1
        ring
      rw [he 2,he 1]
  · simp only [KPGlobalFiniteSIntertwiner.normalizer,GlobalZetaNormalizer.exceptionalNormalizer]
    field_simp

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorFactorLimit

end
