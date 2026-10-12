module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.DeformedTestSupportAndReverseIntegralSymmetry

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPTameJacquetTestDuality KPLocalExceptionalConstruction

private theorem ball_add_subgroup
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ) (r : ℕ) :
    ∃ A : AddSubgroup (LocalField F q), (A : Set (LocalField F q)) = expandingBall F q π r := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  let A := (valuation (LocalField F q)).integer.toAddSubgroup.map
    (AddMonoidHom.mulLeft a)
  refine ⟨A, ?_⟩
  ext x
  change (∃ y, y ∈ (valuation (LocalField F q)).integer ∧ a * y = x) ↔
    ∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, h.symm⟩
  · rintro ⟨u, h⟩
    exact ⟨u, u.property, h.symm⟩

private theorem ball_mono
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    {r s : ℕ} (hrs : r ≤ s) : expandingBall F q π r ⊆ expandingBall F q π s := by
  have hv : valuation (LocalField F q) (π : LocalField F q) ≤ 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.le_iff_le.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) ≤
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  rintro x ⟨u, rfl⟩
  have hn : (π : LocalField F q) ^ (s-r) ∈ (valuation (LocalField F q)).integer :=
    (valuation (LocalField F q)).integer.pow_mem ((Valuation.mem_integer_iff _ _).mpr hv) _
  refine ⟨⟨(π : LocalField F q) ^ (s-r) * u, (valuation (LocalField F q)).integer.mul_mem hn u.property⟩, ?_⟩
  change ((π : LocalField F q)^r)⁻¹ * u = ((π : LocalField F q)^s)⁻¹ * ((π : LocalField F q)^(s-r) * u)
  have he : (π : LocalField F q) ^ s = (π : LocalField F q) ^ r * (π : LocalField F q) ^ (s-r) := by
    rw [← pow_add, Nat.add_sub_of_le hrs]
  rw [he, mul_inv_rev]
  field_simp

private theorem ball_measurable
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ) (r : ℕ) : MeasurableSet (expandingBall F q π r) := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have he : expandingBall F q π r =
      (fun x : LocalField F q => x / a) ⁻¹' ((valuation (LocalField F q)).integer : Set (LocalField F q)) := by
    ext x
    change (∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)) ↔ _
    constructor
    · rintro ⟨u, rfl⟩
      simpa [ha, mul_div_cancel_left₀] using u.property
    · intro hx
      exact ⟨⟨x/a, hx⟩, (mul_div_cancel₀ x ha).symm⟩
  rw [he]
  exact (valuation (LocalField F q)).isOpen_integer.measurableSet.preimage (by fun_prop)

theorem exists_conductor_one_translation
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ) :
    ∃ t ∈ expandingBall F q π 1, ψ (Multiplicative.ofAdd (-t)) ≠ 1 := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hni : (π : LocalField F q)⁻¹ ∉ (valuation (LocalField F q)).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact not_le.mpr (one_lt_inv₀ ((Valuation.pos_iff (valuation (LocalField F q))).mpr π.ne_zero) |>.mpr hv)
  have hw := mt (hconductor ((π : LocalField F q)⁻¹)).mp hni
  push Not at hw
  obtain ⟨o, ho⟩ := hw
  refine ⟨-((o : LocalField F q) * (π : LocalField F q)⁻¹), ?_, ?_⟩
  · refine ⟨-o, ?_⟩
    simp [expandingBall, mul_comm]
  · simpa only [neg_neg] using ho

theorem integral_zero_of_translation
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (t : LocalField F q) (htball : t ∈ expandingBall F q π 1)
    (ht : ψ (Multiplicative.ofAdd (-t)) ≠ 1)
    (φ : LocalField F q → ℂ) (r : ℕ) (hr : 2 ≤ r)
    (hφ : ∀ x ∈ expandingBall F q π r \ expandingBall F q π (r-1),
      φ (x+t) = φ x) :
    (∫ x in expandingBall F q π r \ expandingBall F q π (r-1),
      φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) = 0 := by
  let shell := expandingBall F q π r \ expandingBall F q π (r-1)
  let g := fun x : LocalField F q => φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ)
  have hball : ∀ s : ℕ, 1 ≤ s → ∀ x : LocalField F q,
      x+t ∈ expandingBall F q π s ↔ x ∈ expandingBall F q π s := by
    intro s hs x
    obtain ⟨A, hA⟩ := ball_add_subgroup F q π s
    have htA : t ∈ A := by
      rw [← SetLike.mem_coe, hA]
      exact ball_mono F q π hπ hs htball
    rw [← hA]
    exact A.add_mem_cancel_right htA
  have hset : ∀ x, x+t ∈ shell ↔ x ∈ shell := by
    intro x
    exact and_congr (hball r (by omega) x) (not_congr (hball (r-1) (by omega) x))
  have hms : MeasurableSet shell := (ball_measurable F q π r).diff (ball_measurable F q π (r-1))
  let c : ℂ := (ψ (Multiplicative.ofAdd (-t)) : ℂ)
  have hc : c ≠ 1 := fun h => ht (Units.ext h)
  have hg : ∀ x ∈ shell, g (x+t) = c * g x := by
    intro x hx
    change φ (x+t) * (ψ (Multiplicative.ofAdd (-(x+t))) : ℂ) =
      (ψ (Multiplicative.ofAdd (-t)) : ℂ) * (φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ))
    rw [hφ x hx, neg_add, ofAdd_add, map_mul, Units.val_mul]
    ring
  have hind : ∀ x, shell.indicator g (x+t) = c * shell.indicator g x := by
    intro x
    by_cases hx : x ∈ shell
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hset x).mpr hx), hg x hx]
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hset x).mp hx), mul_zero]
  have he := integral_add_right_eq_self (shell.indicator g) t (μ := μ)
  simp_rw [hind] at he
  rw [integral_const_mul, integral_indicator hms] at he
  have hz : (c-1) * (∫ x in shell, g x ∂μ) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation

end

end
