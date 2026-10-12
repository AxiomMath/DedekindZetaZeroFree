module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RationalFourierExpansion
public import DedekindZetaZeroFree.Theta.Digits.ResidueAverages

@[expose] public section

namespace DedekindZetaZeroFree
namespace ThetaDigitDescent

noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]

def residueComparison (A : SArithmeticData F) (p : KPFinitePlace F)
    (hp : p ∉ A.Sf) :
    ThetaDigitAverage.Residue p ≃+*
      (A.R ⧸ Ideal.map (algebraMap (𝓞 F) A.R) p.asIdeal) :=
  Classical.choose (ThetaDigitAverage.residue_SInteger_comparison A p hp)

def residueSixthUnit (A : SArithmeticData F) (p : KPFinitePlace F)
    (hp : p ∉ A.Sf) (u : A.U) : (ThetaDigitAverage.Residue p)ˣ :=
  Units.map (residueComparison A p hp).symm.toRingHom.toMonoidHom
    (Units.map (Ideal.Quotient.mk _).toMonoidHom (A.unitEquiv u ^ 6))

def reindex (A : SArithmeticData F) (P : Finset (KPFinitePlace F))
    (hP : ∀ p ∈ P, p ∉ A.Sf) (u : A.U) :
    ThetaDigitAverage.Dig P ≃ ThetaDigitAverage.Dig P :=
  Equiv.piCongrRight (fun p => (residueSixthUnit A p.val
    (hP p.val p.property) u).mulLeft)

section KP

theorem chi_sixth_pow_eq_one {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (hχ : orderOf χ = 6) {x : k} (hx : x ≠ 0) : χ (x ^ 6) = 1 := by
  have h6 : χ ^ 6 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have hx6 : χ x ^ 6 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num : (6 : ℕ) ≠ 0) x, h6]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  rw [map_pow, hx6]

theorem sexticFourierMask_mul_eq {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : orderOf χ = 6)
    {γ : k} (hγ : χ γ = 1) (j : Fin 6) (v : k) :
    sexticFourierMask χ ψ j (γ * v) = sexticFourierMask χ ψ j v := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, MulChar.map_nonunit χ (by simp [IsUnit])] at hγ
    exact one_ne_zero hγ.symm
  have hzv : γ * v = 0 ↔ v = 0 := by
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_left hγ0
    · intro h; rw [h, mul_zero]
  by_cases hj : j.val = 0
  · have hmask (w : k) : sexticFourierMask χ ψ j w =
        if w = 0 then 1 - (Fintype.card k : ℂ)⁻¹ else -(Fintype.card k : ℂ)⁻¹ := by
      simp only [sexticFourierMask, if_pos hj]
    rw [hmask, hmask]
    by_cases hv : v = 0
    · subst hv; simp [sexticFourierMask, if_pos hj]
    · rw [if_neg hv, if_neg (fun h => hv (hzv.mp h))]
  · have hg : (χ⁻¹ ^ j.val) γ = 1 := by
      rw [MulChar.pow_apply' χ⁻¹ hj γ, MulChar.inv_apply_eq_inv', hγ, inv_one, one_pow]
    have hγv : (χ⁻¹ ^ j.val) (γ * v) = (χ⁻¹ ^ j.val) v := by
      rw [map_mul, hg, one_mul]
    have hmask (w : k) (hw : w ≠ 0) : sexticFourierMask χ ψ j w =
        (χ⁻¹ ^ j.val) w / sexticMaskGaussSum χ ψ j := by
      simp only [sexticFourierMask, if_neg hj, if_neg hw]
    by_cases hv : v = 0
    · subst hv; simp [sexticFourierMask, if_neg hj]
    · rw [hmask (γ * v) (mul_ne_zero hγ0 hv), hmask v hv, hγv]

def scale (t : F) : KPAdditiveQuotient F →+ KPAdditiveQuotient F := by
  let S := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let m : KPAdeles F →+ KPAdeles F :=
    { toFun := fun z => algebraMap F (KPAdeles F) t * z
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  apply QuotientAddGroup.lift S ((QuotientAddGroup.mk' S).comp m)
  rintro z ⟨s, rfl⟩
  change QuotientAddGroup.mk (algebraMap F (KPAdeles F) t *
    algebraMap F (KPAdeles F) s) = 0
  rw [← map_mul]
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨t * s, rfl⟩

theorem scale_mk (t : F) (x : KPAdeles F) :
    scale (F := F) t (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (algebraMap F (KPAdeles F) t * x) := rfl

theorem scale_continuous (t : F) : Continuous (scale (F := F) t) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (NumberField.AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  change Continuous (fun z : KPAdeles F => scale (F := F) t (QuotientAddGroup.mk z))
  simp_rw [scale_mk]
  exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)

theorem scale_inverse (q : Fˣ) (z : KPAdditiveQuotient F) :
    scale (F := F) (q⁻¹ : Fˣ) (scale (F := F) (q : F) z) = z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [scale_mk, scale_mk, ← mul_assoc, ← map_mul,
    Units.inv_mul, map_one, one_mul]

end KP
end
end ThetaDigitDescent
end DedekindZetaZeroFree
