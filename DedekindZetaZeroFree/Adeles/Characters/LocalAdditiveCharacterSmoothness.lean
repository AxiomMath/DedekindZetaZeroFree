module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.NonarchimedeanWhittakerBounds

@[expose] public section

noncomputable section
open scoped NumberField Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPJacquetCharacter

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

abbrev AdditiveCharacter := AddChar (v.adicCompletion F) ℂˣ

private theorem character_norm_le_one (ψ : AdditiveCharacter F v)
    (hψ : Continuous ψ) (x : v.adicCompletion F) : ‖(ψ x : ℂ)‖ ≤ 1 := by
  have hc := (isCompact_closedBall (0 : v.adicCompletion F) ‖x‖).image
    (Units.continuous_val.comp hψ)
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hc.isBounded
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
  have hx : n • x ∈ Metric.closedBall (0 : v.adicCompletion F) ‖x‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, nsmul_eq_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg x)
      (IsUltrametricDist.norm_natCast_le_one _ n)
  have hb := hC (Set.mem_image_of_mem (fun y => (ψ y : ℂ)) hx)
  have hpow : ‖(ψ x : ℂ)‖ ^ n ≤ C := by
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    simpa only [AddChar.map_nsmul_eq_pow, Units.val_pow_eq_pow_val, norm_pow] using hb
  exact (not_lt_of_ge hpow) hn

theorem character_unitary (ψ : AdditiveCharacter F v) (hψ : Continuous ψ)
    (x : v.adicCompletion F) : ‖(ψ x : ℂ)‖ = 1 := by
  apply le_antisymm (character_norm_le_one F v ψ hψ x)
  have hi := character_norm_le_one F v ψ hψ (-x)
  rw [AddChar.map_neg_eq_inv, Units.val_inv_eq_inv_val, norm_inv] at hi
  have hp : 0 < ‖(ψ x : ℂ)‖ := norm_pos_iff.mpr (ψ x).ne_zero
  exact (inv_le_one₀ hp).mp hi

def circleCharacter (ψ : AdditiveCharacter F v) (hψ : Continuous ψ) :
    AddChar (v.adicCompletion F) Circle where
  toFun x := ⟨(ψ x : ℂ), by
    exact mem_sphere_zero_iff_norm.2 (character_unitary F v ψ hψ x)⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' x y := by
    apply Circle.ext
    change (ψ (x + y) : ℂ) = (ψ x : ℂ) * (ψ y : ℂ)
    simp [AddChar.map_add_eq_mul]

@[simp] theorem circleCharacter_coe (ψ : AdditiveCharacter F v) (hψ : Continuous ψ)
    (x : v.adicCompletion F) : (circleCharacter F v ψ hψ x : ℂ) = (ψ x : ℂ) := rfl

theorem continuous_circleCharacter (ψ : AdditiveCharacter F v) (hψ : Continuous ψ) :
    Continuous (circleCharacter F v ψ hψ) := by
  exact (Units.continuous_val.comp hψ).subtype_mk _

theorem character_trivial_near_zero (ψ : AdditiveCharacter F v) (hψ : Continuous ψ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : v.adicCompletion F, ‖x‖ < r → ψ x = 1 := by
  obtain ⟨r, hr, hb⟩ := KPFiniteLocal.character_trivial_near_zero
    (circleCharacter F v ψ hψ) (continuous_circleCharacter F v ψ hψ)
  refine ⟨r, hr, fun x hx => ?_⟩
  apply Units.ext
  simpa using congrArg (fun z : Circle => (z : ℂ)) (hb x hx)

theorem character_locallyConstant (ψ : AdditiveCharacter F v) (hψ : Continuous ψ) :
    IsLocallyConstant ψ := by
  obtain ⟨r, hr, hb⟩ := character_trivial_near_zero F v ψ hψ
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hsub : ψ (y - x) = 1 := hb (y - x) (by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  rw [AddChar.map_sub_eq_div, div_eq_one] at hsub
  exact hsub

end DedekindZetaZeroFree.KPJacquetCharacter

end
