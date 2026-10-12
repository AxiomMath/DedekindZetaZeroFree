module

public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.BorelCharacter

@[expose] public section

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPActualReflectionData.ScalarFiberInverse
open KPGlobalResidualConstruction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => KPGlobalTorusFunctionData.E F ζ hζ
local notation "Q" => KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ

 theorem half_ne_zero (t : E) : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)))

 theorem half_mul (t u : E) :
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ (t*u) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t * KPGlobalTorusFunctionData.deltaHalf F ζ hζ u := by
  simp [KPGlobalTorusFunctionData.deltaHalf, map_mul, Units.val_mul, NNReal.coe_mul,
    Real.sqrt_mul (show (0 : ℝ) ≤ ((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ) by positivity),
    Complex.ofReal_mul]

private theorem half_one : KPGlobalTorusFunctionData.deltaHalf F ζ hζ (1 : E) = 1 := by
  simp [KPGlobalTorusFunctionData.deltaHalf]

 theorem scalar_torus_covariance (h : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (r : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).H) (g : G F ζ hζ) : h.val (r.val.val * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val * ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character r : ℂ) * h.val g := by
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 := (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simpa only [hn, mul_one] using h.property r 0 g

def fiber (h : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q) (g : G F ζ hζ) :
    RationalFiber F ζ hζ :=
  ⟨fun t => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * h.val (t.val * g), by
    intro r t
    dsimp only
    rw [Subgroup.coe_mul, mul_assoc, scalar_torus_covariance, half_mul]
    field_simp [half_ne_zero F ζ hζ r.val, half_ne_zero F ζ hζ t]
    change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * h.val (t.val*g) =
      h.val (t.val*g) * (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ)
    ring⟩

 theorem fiber_covariance (h : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (t : E) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) (u : E) :
    (fiber F ζ hζ h ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val u =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
        (fiber F ζ hζ h g).val (u*t) := by
  have hN : ∀ (a : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ),
      h.val (KPGlobalTorusFunctionData.N F ζ hζ a * g) = h.val g := by
    intro a g
    simpa [half_one F ζ hζ] using h.property (1 : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).H) a g
  have he : (u.val * t.val) * KPGlobalTorusFunctionData.N F ζ hζ x * g =
      KPGlobalTorusFunctionData.N F ζ hζ ((KPGlobalTorusFunctionData.p F ζ hζ (u*t)).val * x) *
        ((u*t).val * g) := by
    have hc := ActualBorelRetraction.torus_conjugates_root F ζ hζ (u*t) x
    calc
      _ = ((u*t).val * KPGlobalTorusFunctionData.N F ζ hζ x * (u*t).val⁻¹) * ((u*t).val*g) := by
        rw [Subgroup.coe_mul]
        group
      _ = _ := by rw [hc]
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ u)⁻¹ * h.val
    (u.val * ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)) = _
  rw [← mul_assoc, ← mul_assoc, he, hN]
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
    ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ (u*t))⁻¹ * h.val ((u*t).val*g))
  rw [half_mul]
  field_simp [half_ne_zero F ζ hζ u, half_ne_zero F ζ hζ t]

end DedekindZetaZeroFree.KPActualReflectionData.ScalarFiberInverse

end

end

section

noncomputable section
open scoped NumberField Classical NNReal Topology
namespace DedekindZetaZeroFree.KPActualReflectionData.SmoothScalarInverse
open KPGlobalResidualConstruction
open ScalarFiberInverse
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => KPGlobalTorusFunctionData.E F ζ hζ
local notation "Q" => KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ

private theorem rational_arch_character (z : KPGlobalTorusFunctionData.TorusArch F) :
    ∃ r : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).H,
      r.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
      ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character r : ℂ) =
        KPGlobalTorusBorelNormTwistTransport.normPower F ζ hζ (1/6) r.val := by
  obtain ⟨h, he, hc⟩ := ActualRaisingGeometry.source_arch_chart_character F ζ hζ z
  have hz : KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0 =
      KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ :=
    KPContFlatSourceRecipe.sourcePolarization_zero F ζ hζ
  let r : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).H :=
    ⟨h.val, by rw [← hz]; exact h.property⟩
  refine ⟨r, he, ?_⟩
  have hchar : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character r =
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h := by
    have general (P₁ P₂ : KPGlobalTorusFunctionData.Polarization F ζ hζ)
        (he : P₂ = P₁) (h : P₂.H) :
        P₁.character ⟨h.val, by rw [← he]; exact h.property⟩ = P₂.character h := by
      cases he
      rfl
    exact general _ _ hz h
  rw [hchar, hc]
  change (((KPGlobalCenterRationalCharacter.nu F ζ hζ h.val : ℝ≥0) : ℝ) : ℂ) = _
  rw [KPGlobalCenterRationalCharacter.nu_formula]
  change ((((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = _
  have hd : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ h.val)))
  rw [Real.rpow_def_of_pos hd, Complex.ofReal_exp]
  simp only [KPGlobalTorusBorelNormTwistTransport.normPower, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  congr 1
  change _ = (1/6 : ℂ) * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ)) : ℂ)
  push_cast
  ring

theorem rational_fiber_archSmooth (f : RationalFiber F ζ hζ) :
    f ∈ KPGlobalTorusFunctionData.ArchSmooth
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).H
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
  intro t
  have he : (fun z => f.val (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t)) =
      fun z => KPGlobalTorusBorelNormTwistTransport.normPower F ζ hζ (1/6)
        (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z) * f.val t := by
    funext z
    obtain ⟨r, hr, hc⟩ := rational_arch_character F ζ hζ z
    rw [← hr, f.property r t]
    change ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character r : ℂ) * _ = _
    rw [hc]
  rw [he]
  have hs := KPGlobalTorusBorelNormTwistTransport.normPowerArchSmooth_of_chart_formula F ζ hζ
    (KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ) (1/6)
  simpa using (show ContDiffOn ℝ (⊤ : ℕ∞) _ _ from hs (1 : E)).mul contDiffOn_const

theorem fiber_mem_smoothUnion
    (h : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hJ : ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      h.val (g * j.val) = h.val g) (g : G F ζ hζ) :
    fiber F ζ hζ h g ∈ KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q := by
  obtain ⟨U,hc,hconj⟩ :=
    KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel.exists_compact_conjugate_torus_level F ζ hζ J g
  apply (le_iSup (fun U => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) U)
  constructor
  · exact rational_fiber_archSmooth F ζ hζ _
  · intro t
    apply Subtype.ext
    funext u
    have hd := KPGlobalTorusBorelNormTwistTransport.delta_compact_subgroup F ζ hζ _ hc t
    have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val = 1 := by
      simp [KPGlobalTorusFunctionData.deltaHalf, hd]
    have hmul : KPGlobalTorusFunctionData.deltaHalf F ζ hζ (u * t.val) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ u := by
      simp [KPGlobalTorusFunctionData.deltaHalf, map_mul, hd]
    change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ (u*t.val))⁻¹ * h.val ((u*t.val).val*g) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ u)⁻¹ * h.val (u.val*g)
    rw [hmul, Subgroup.coe_mul]
    have hm : (u.val*t.val.val)*g = (u.val*g)*(g⁻¹*t.val.val*g) := by group
    rw [hm, hJ _ ⟨_, hconj t⟩]

end DedekindZetaZeroFree.KPActualReflectionData.SmoothScalarInverse

end

end
