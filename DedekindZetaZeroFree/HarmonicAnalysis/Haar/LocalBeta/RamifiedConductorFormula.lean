module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CubicBeta.ConductorAnnuliAndShellSeries

@[expose] public section

namespace DedekindZetaZeroFree
namespace KPRamifiedBeta

open scoped ValuativeRel Topology
open MeasureTheory Filter

noncomputable def normalizedAbs (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else
    (CubicUnitCharacters.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x))

noncomputable def multiplicativeMeasure (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
    (μ : Measure K) : Measure K :=
  μ.withDensity (fun x ↦ ENNReal.ofReal ((normalizedAbs K x)⁻¹))

noncomputable def unitsInclusion (K : Type*) [Field K] [ValuativeRel K] :
    (𝒪[K])ˣ →* Kˣ :=
  Units.map (𝒪[K]).subtype.toMonoidHom

noncomputable def integrand (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) (x : K) : ℂ := by
  classical
  exact if hx : x = 0 then 0 else
    (χ (Units.mk0 x hx) : ℂ) * (normalizedAbs K (1 - x) : ℂ) ^ (-s)

noncomputable def betaIntegral (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
    (μ : Measure K) (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, integrand K χ s x ∂multiplicativeMeasure K μ

noncomputable def rationalBeta (q m : ℝ) (f : ℕ) (L : ℂ) : ℂ :=
  (m : ℂ) * ((q : ℂ)⁻¹) ^ f * L ^ (f - 1) * (L - 1) /
    (1 - (q : ℂ)⁻¹ * L)

open Filter
open scoped Topology

theorem rationalBeta_shell_sum (q m : ℝ) (f : ℕ) (hf : 1 ≤ f) (L : ℂ)
    (h : ‖(q : ℂ)⁻¹ * L‖ < 1) :
    (m : ℂ) * (1 - (q : ℂ)⁻¹) * (∑' j : ℕ, ((q : ℂ)⁻¹ * L) ^ (j + f))
        - (m : ℂ) * ((q : ℂ)⁻¹) ^ f * L ^ (f - 1)
      = rationalBeta q m f L := by
  set a : ℂ := (q : ℂ)⁻¹ with ha
  have hgeom : (∑' j : ℕ, (a * L) ^ (j + f)) = (a * L) ^ f / (1 - a * L) := by
    rw [show (fun j : ℕ => (a * L) ^ (j + f)) = (fun j : ℕ => (a * L) ^ f * (a * L) ^ j) by
      funext j; rw [pow_add, mul_comm]]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by simpa [ha] using h), div_eq_mul_inv]
  rw [hgeom, rationalBeta, ha]
  rw [mul_pow, div_eq_mul_inv]
  have hLf : L ^ f = L ^ (f - 1) * L := by
    conv_lhs =>
      rw [show f = (f - 1) + 1 by omega]
      rw [pow_succ]
  rw [hLf]
  have hne : (1 : ℂ) - (q : ℂ)⁻¹ * L ≠ 0 := by
    intro h0
    have h1 : (q : ℂ)⁻¹ * L = 1 := by
      have := sub_eq_zero.mp h0
      exact this.symm
    have := h
    rw [h1, norm_one] at this
    exact lt_irrefl 1 this
  have hDd : (1 - (q : ℂ)⁻¹ * L)⁻¹ * (1 - (q : ℂ)⁻¹ * L) = 1 := inv_mul_cancel₀ hne
  linear_combination ((m : ℂ) * (q : ℂ)⁻¹ ^ f * L ^ (f - 1)) * hDd

end KPRamifiedBeta

end DedekindZetaZeroFree
