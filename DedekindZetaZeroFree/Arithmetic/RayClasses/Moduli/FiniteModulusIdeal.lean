module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

def finiteModulusIdeal (c : ClassFieldTheory.RayClassModulus F) : Ideal (𝓞 F) :=
  c.finitePart.prod (fun p n => p.asIdeal ^ n)

private lemma coe_finiteModulusIdeal (c : ClassFieldTheory.RayClassModulus F) :
    (finiteModulusIdeal c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      ∏ p ∈ c.finitePart.support,
        ((p.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ c.finitePart p) := by
  rw [finiteModulusIdeal, Finsupp.prod]
  rw [show ((∏ p ∈ c.finitePart.support, p.asIdeal ^ c.finitePart p : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F
        (∏ p ∈ c.finitePart.support, p.asIdeal ^ c.finitePart p) from rfl]
  rw [map_prod]
  exact Finset.prod_congr rfl fun p _ =>
    FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 F)) F p.asIdeal _

private lemma count_coe_finiteModulusIdeal (c : ClassFieldTheory.RayClassModulus F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v
        (finiteModulusIdeal c : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (c.finitePart v : ℤ) := by
  rw [coe_finiteModulusIdeal, FractionalIdeal.count_prod]
  · rw [Finset.sum_congr rfl fun p _ => by
      rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal, mul_ite, mul_one, mul_zero]]
    rw [Finset.sum_ite_eq' c.finitePart.support v (fun p => (c.finitePart p : ℤ))]
    split_ifs with hv
    · rfl
    · have hv' : c.finitePart v = 0 := by
        by_contra h
        exact hv (Finsupp.mem_support_iff.mpr h)
      simp [hv']
  · intro p _
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

private lemma sup_eq_top_iff_of_isMaximal {I J : Ideal (𝓞 F)} (hI : I.IsMaximal) :
    I ⊔ J = ⊤ ↔ ¬ J ≤ I := by
  constructor
  · intro h hle
    exact hI.ne_top (top_le_iff.mp (h ▸ sup_le le_rfl hle))
  · intro h
    by_contra hne
    exact h ((hI.eq_of_le hne le_sup_left) ▸ le_sup_right)

theorem finiteModulusIdeal_ne_bot (c : ClassFieldTheory.RayClassModulus F) :
    finiteModulusIdeal c ≠ ⊥ := by
  rw [← FractionalIdeal.coeIdeal_ne_zero (K := F)]
  rw [coe_finiteModulusIdeal, Finset.prod_ne_zero_iff]
  intro p _
  exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

@[simp] theorem fullModulus_finiteModulusIdeal_finitePart
    (c : ClassFieldTheory.RayClassModulus F) :
    (DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus (finiteModulusIdeal c)
      (finiteModulusIdeal_ne_bot c)).finitePart = c.finitePart := by
  ext v
  rw [DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus_finitePart]
  have h := FractionalIdeal.count_coe (K := F) (v := v) (finiteModulusIdeal_ne_bot c)
  rw [count_coe_finiteModulusIdeal c v] at h
  exact (Nat.cast_injective h).symm

theorem mem_finitePart_support_iff
    (c : ClassFieldTheory.RayClassModulus F)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    p ∈ c.finitePart.support ↔ p.asIdeal ⊔ finiteModulusIdeal c ≠ ⊤ := by
  have hg := finiteModulusIdeal_ne_bot c
  have hcount : (Associates.mk p.asIdeal).count
      (Associates.mk (finiteModulusIdeal c)).factors = c.finitePart p := by
    have h := FractionalIdeal.count_coe (K := F) (v := p) hg
    rw [count_coe_finiteModulusIdeal c p] at h
    exact (Nat.cast_injective h).symm
  rw [Finsupp.mem_support_iff, ← hcount, Associates.count_ne_zero_iff_dvd hg p.irreducible,
    Ideal.dvd_iff_le]
  constructor
  · intro hle h
    exact ((sup_eq_top_iff_of_isMaximal (I := p.asIdeal) (J := finiteModulusIdeal c)
      p.isMaximal).mp h) hle
  · intro hne
    by_contra hle
    exact hne ((sup_eq_top_iff_of_isMaximal (I := p.asIdeal) (J := finiteModulusIdeal c)
      p.isMaximal).mpr hle)

@[simp] theorem fullModulus_finiteModulusIdeal
    (hF : NumberField.IsTotallyComplex F) (c : ClassFieldTheory.RayClassModulus F) :
    DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus (finiteModulusIdeal c)
      (finiteModulusIdeal_ne_bot c) = c := by
  haveI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hF.isComplex v.1)) v.2⟩
  refine ClassFieldTheory.RayClassModulus.ext (fullModulus_finiteModulusIdeal_finitePart c) ?_
  rw [DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus_infinitePart]
  exact Subsingleton.elim _ _

end DedekindZetaZeroFree.LargeSieve.RootNumber

end
