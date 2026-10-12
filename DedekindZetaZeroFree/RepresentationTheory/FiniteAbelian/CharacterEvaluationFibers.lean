module

public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem dualEvaluation_orderOf_pos
    {G : Type*} [CommGroup G] [Finite G] (g : G) :
    0 < orderOf g := by
  exact orderOf_pos g

theorem dualEvaluation_pow_orderOf
    {G : Type*} [CommGroup G] [Finite G] (g : G) (ρ : ComplexDual G) :
    (ρ g) ^ orderOf g = 1 := by
  rw [← map_pow, pow_orderOf_eq_one, map_one]

theorem dualEvaluationFibers
    {G : Type*} [CommGroup G] [Finite G] (g : G)
    (ζ : ℂˣ) (hζ : ζ ^ orderOf g = 1) :
    Nat.card {ρ : ComplexDual G // ρ g = ζ} = Nat.card G / orderOf g := by
  classical
  let H := Subgroup.zpowers g
  let x : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hx : ∀ y : H, y ∈ Subgroup.zpowers x := by
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
  have horder : orderOf ζ ∣ orderOf x := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hζ
  let φ : H →* ℂˣ := monoidHomOfForallMemZpowers hx horder
  have hφ : φ x = ζ := monoidHomOfForallMemZpowers_apply_gen hx horder
  obtain ⟨ρ₀, hρ₀⟩ := MonoidHom.domRestrict_surjective (M := ℂ) H φ
  have hvalue : ρ₀ g = ζ := by
    exact (DFunLike.congr_fun hρ₀ x).trans hφ
  let ev : ComplexDual G →* ℂˣ :=
    { toFun := fun ρ => ρ g
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : ev.ker = (MonoidHom.domRestrictHom H ℂˣ).ker := by
    ext ρ
    change ρ g = 1 ↔ ρ.domRestrict H = 1
    rw [MonoidHom.eq_iff_eq_on_generator hx]
    rfl
  have hfiber : Nat.card {ρ : ComplexDual G // ρ g = ζ} = Nat.card ev.ker := by
    rw [← hvalue]
    exact Nat.card_congr (ev.fiberEquivKer ρ₀)
  rw [hfiber, hker, CommGroup.card_domRestrictHom_ker (M := ℂ)]
  rw [H.card_eq_card_quotient_mul_card_subgroup, Nat.card_zpowers]
  exact (Nat.mul_div_cancel _ (dualEvaluation_orderOf_pos g)).symm

end DedekindZetaZeroFree.AbelianQuotient
