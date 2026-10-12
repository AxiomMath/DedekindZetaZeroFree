module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.GlobalIntegralContinuation
public import DedekindZetaZeroFree.Arithmetic.LocalFields.Integration.CubicShellSummation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.ScalarChamberReduction

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Valued Classical
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
open MeasureTheory ValuativeRel KPLocalPrincipalSeries
open KPRankOneTameSphericalFactor KPRankOneRootParameter KPRankOneShellContinuation
open KPExceptionalRaw.FiniteSource.GoodSphericalVector

theorem integral_of_geometric_cubic_shells
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) (H : K → ℂ) (a b r : ℂ) (hr : ‖r‖ < 1)
    (hInt : Integrable H μ)
    (hBall : (∫ x in ((valuation K).integer : Set K), H x ∂μ) = a)
    (hShell : ∀ n : ℕ, (∫ x in negativeValuationShell K n, H x ∂μ) =
      if 3 ∣ n + 1 then (1 - b) * r ^ ((n + 1) / 3) * a else 0) :
    (∫ x, H x ∂μ) = ((1 - b * r) / (1 - r)) * a := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hm (n : ℕ) : MeasurableSet (negativeValuationShell K n) := by
    apply IsOpen.measurableSet
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : valuation K x ≠ 0 := by
      intro h
      have hh := hx
      change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hh
      simp [h] at hh
    filter_upwards [(valuation K).locally_const hx0] with y hy
    change e (valuation K y) = WithZero.exp ((n + 1 : ℕ) : ℤ)
    change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hx
    simpa only [hy] using hx
  have hd : Pairwise (fun n m => Disjoint (negativeValuationShell K n) (negativeValuationShell K m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    have hh : WithZero.exp ((n + 1 : ℕ) : ℤ) =
        WithZero.exp ((m + 1 : ℕ) : ℤ) := hxn.symm.trans hxm
    have hh' := WithZero.exp_injective hh
    omega
  have hc : (⋃ n : ℕ, negativeValuationShell K n) =
      ((valuation K).integer : Set K)ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    change (∃ n, x ∈ negativeValuationShell K n) ↔ ¬ valuation K x ≤ 1
    rw [not_le]
    constructor
    · rintro ⟨n, hn⟩
      have he : 1 < e (valuation K x) := by
        change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hn
        rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      apply (map_lt_map_iff e).mp
      simpa only [map_one] using he
    · intro hx
      have he : 1 < e (valuation K x) := by
        simpa only [map_one] using (e.strictMono hx)
      have hne : e (valuation K x) ≠ 0 := ne_of_gt (lt_trans zero_lt_one he)
      let z := WithZero.log (e (valuation K x))
      have hz : 0 < z := by
        have hh := WithZero.exp_log hne
        rw [← hh, ← WithZero.exp_zero, WithZero.exp_lt_exp] at he
        exact he
      refine ⟨z.toNat - 1, ?_⟩
      change e (valuation K x) = WithZero.exp (((z.toNat - 1) + 1 : ℕ) : ℤ)
      have hzn : (((z.toNat - 1) + 1 : ℕ) : ℤ) = z := by
        have := Int.toNat_of_nonneg (le_of_lt hz)
        omega
      rw [hzn]
      exact (WithZero.exp_log hne).symm
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have he : r = 1 := by linear_combination -h
    simpa [he] using hr
  let f : ℕ → ℂ := fun n => if 3 ∣ n + 1 then (1 - b) * r ^ ((n + 1) / 3) * a else 0
  let j : ℕ → ℕ := fun k => 3 * (k + 1) - 1
  have hj : Function.Injective j := by
    intro k l h
    dsimp [j] at h
    omega
  have hf0 : ∀ n ∉ Set.range j, f n = 0 := by
    intro n hn
    dsimp [f]
    apply if_neg
    intro hdvd
    apply hn
    refine ⟨(n + 1) / 3 - 1, ?_⟩
    have hh := Nat.div_mul_cancel hdvd
    dsimp [j]
    omega
  have hfj (k : ℕ) : f (j k) = (1 - b) * r ^ (k + 1) * a := by
    have h1 : j k + 1 = 3 * (k + 1) := by dsimp [j]; omega
    have h2 : 3 ∣ j k + 1 := by rw [h1]; exact dvd_mul_right 3 (k + 1)
    simp only [f, if_pos h2, h1, Nat.mul_div_right _ (by decide : 0 < 3)]
  have hg : HasSum (fun k : ℕ => (1 - b) * r ^ (k + 1) * a) ((1 - b) * r / (1 - r) * a) := by
    have hh := ((hasSum_geometric_of_norm_lt_one hr).mul_left ((1 - b) * r)).mul_right a
    change HasSum _ ((1 - b) * r * (1 - r)⁻¹ * a) at hh
    have he : (fun k : ℕ => (1 - b) * r ^ (k + 1) * a) =
        (fun k : ℕ => (1 - b) * r * r ^ k * a) := by
      funext k
      simp only [pow_succ]
      ring
    rw [he]
    simpa only [div_eq_mul_inv] using hh
  have hf : HasSum f ((1 - b) * r / (1 - r) * a) := by
    apply (hj.hasSum_iff hf0).mp
    simpa only [Function.comp_def, hfj] using hg
  have hsum := hasSum_integral_iUnion hm hd (hInt.integrableOn)
  have hsum' : HasSum f (∫ x in ((valuation K).integer : Set K)ᶜ, H x ∂μ) := by
    simpa only [hc, hShell, f] using hsum
  have ht : (∫ x in ((valuation K).integer : Set K)ᶜ, H x ∂μ) =
      (1 - b) * r / (1 - r) * a := hsum'.unique hf
  rw [← integral_add_compl ((valuation K).isOpen_integer.measurableSet) hInt, hBall, ht]
  field_simp
  <;> ring

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
  {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : KPLocalStoneVonNeumann.LocalHeisenbergData H D}

theorem spherical_integer_ball_integral
    (A : LocalBorelData (K := K) (G := G) T)
    (P : KPLocalStoneVonNeumann.Polarization T) (I : IwasawaData A)
    (μ : Measure K) (φ : compactPicture A P I .plus)
    (hφ : IsSphericalVector K A P I .plus φ)
    (hw : A.liftedW ∈ I.compact.toOpenSubgroup)
    (hn : ∀ x : (valuation K).integer,
      (A.upperRoot (Multiplicative.ofAdd (x : K)) : G) ∈ I.compact.toOpenSubgroup)
    (s : ℂ) :
    (∫ x in ((valuation K).integer : Set K),
      ((compactTrivialization A P I .plus s φ).val
        (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1 ∂μ) =
      (haarMass K μ : ℂ) := by
  have hm := (valuation K).isOpen_integer.measurableSet
  have hv : Set.EqOn (fun x : K =>
      ((compactTrivialization A P I .plus s φ).val
        (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1)
      (fun _ => (1 : ℂ)) ((valuation K).integer : Set K) := by
    intro x hx
    let k : I.compact.toOpenSubgroup := ⟨_,
      I.compact.toOpenSubgroup.mul_mem (I.compact.toOpenSubgroup.inv_mem hw) (hn ⟨x, hx⟩)⟩
    have hf := congrArg (fun f => (f.val 1).val 1) (hφ.2 s k)
    change ((compactTrivialization A P I .plus s φ).val (1 * (k : G))).val 1 = _ at hf
    rw [one_mul] at hf
    exact hf.trans (hφ.1 s)
  rw [setIntegral_congr_fun hm hv]
  simp [haarMass, Measure.real]

theorem compact_coordinate_deformation
    (A : LocalBorelData (K := K) (G := G) T)
    (P : KPLocalStoneVonNeumann.Polarization T) (I : IwasawaData A)
    (ε : Sign) (φ : compactPicture A P I ε) (s : ℂ) (g : G) (h : H) :
    ((compactTrivialization A P I ε s φ).val g).val h =
      normPower K (A.coordinate (A.retract (I.borelPart g))) s *
        ((compactTrivialization A P I ε 0 φ).val g).val h := by
  change (inducingAction A P ε s (I.borelPart g)
    (φ.val (I.compactPart g))).val h = _ *
      (inducingAction A P ε 0 (I.borelPart g) (φ.val (I.compactPart g))).val h
  change ((deltaHalf A (I.borelPart g) *
      normPower K (A.coordinate (A.retract (I.borelPart g))) s) •
      (borelAction A P ε (I.borelPart g) (φ.val (I.compactPart g)))).val h =
    _ * ((deltaHalf A (I.borelPart g) *
      normPower K (A.coordinate (A.retract (I.borelPart g))) 0) •
      (borelAction A P ε (I.borelPart g) (φ.val (I.compactPart g)))).val h
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, normPower,
    zero_mul, Complex.exp_zero, mul_one]
  ring

theorem normPower_of_valuation_exponent
    (y : Kˣ) (e : ℤ)
    (hy : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) =
      WithZero.exp e) (s : ℂ) :
    normPower K y s = r K s ^ (-e) := by
  have hq : 0 < (residueCardinality K : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := 𝓀[K]))
  simp only [normPower, localAbs, hy, WithZero.log_exp]
  rw [Real.log_rpow hq]
  unfold r
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem spherical_shell_integral_deformation
    (A : LocalBorelData (K := K) (G := G) T)
    (P : KPLocalStoneVonNeumann.Polarization T) (I : IwasawaData A)
    (μ : Measure K) (φ : compactPicture A P I .plus)
    (hcoord : ∀ n : ℕ, ∀ x ∈ negativeValuationShell K n,
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (valuation K (A.coordinate (A.retract (I.borelPart
          (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G)))) : K)) =
          WithZero.exp (-2 * (n + 1 : ℕ) : ℤ))
    (hzero : ∀ n : ℕ,
      (∫ x in negativeValuationShell K n,
        ((compactTrivialization A P I .plus 0 φ).val
          (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1 ∂μ) =
        if 3 ∣ n + 1 then (haarMass K μ : ℂ) *
          (1 - (residueCardinality K : ℂ)⁻¹) *
          ((residueCardinality K : ℂ)⁻¹) ^ ((n + 1) / 3) else 0)
    (s : ℂ) (n : ℕ) :
    (∫ x in negativeValuationShell K n,
      ((compactTrivialization A P I .plus s φ).val
        (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1 ∂μ) =
      if 3 ∣ n + 1 then (haarMass K μ : ℂ) *
        (1 - (residueCardinality K : ℂ)⁻¹) * (t K s) ^ ((n + 1) / 3) else 0 := by
  have hm : MeasurableSet (negativeValuationShell K n) := by
    apply IsOpen.measurableSet
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : valuation K x ≠ 0 := by
      intro h
      have hh := hx
      simp [negativeValuationShell, h] at hh
    filter_upwards [(valuation K).locally_const hx0] with y hy
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K y) = _
    rw [hy]
    exact hx
  have hv : Set.EqOn (fun x : K =>
      ((compactTrivialization A P I .plus s φ).val
        (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1)
      (fun x : K => (r K s) ^ (2 * (n + 1)) *
        ((compactTrivialization A P I .plus 0 φ).val
          (A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G))).val 1)
      (negativeValuationShell K n) := by
    intro x hx
    dsimp only
    rw [compact_coordinate_deformation K A P I .plus φ s _ 1,
      normPower_of_valuation_exponent K _ _ (hcoord n x hx) s]
    have he : -(-2 * (n + 1 : ℕ) : ℤ) = (2 * (n + 1) : ℕ) := by
      push_cast
      ring
    rw [he, zpow_natCast]
  rw [setIntegral_congr_fun hm hv, integral_const_mul, hzero]
  split_ifs with h
  · have hn : 2 * (n + 1) = 6 * ((n + 1) / 3) := by
      have := Nat.div_mul_cancel h
      omega
    rw [hn, pow_mul, t, mul_pow]
    ring
  · simp

theorem spherical_scalar_of_cubic_shell_integrals
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (hφ : IsSphericalVector (LocalField F q) S.borel P S.iwasawa .plus φ)
    (hBall : ∀ s : ℂ, convergenceHalfPlane .plus s →
      (∫ x in ((valuation (LocalField F q)).integer : Set (LocalField F q)),
        ((compactTrivialization S.borel P S.iwasawa .plus s φ).val
          (S.borel.liftedW⁻¹ * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val 1 ∂μ) =
        (haarMass (LocalField F q) μ : ℂ))
    (hShell : ∀ s : ℂ, convergenceHalfPlane .plus s → ∀ n : ℕ,
      (∫ x in negativeValuationShell (LocalField F q) n,
        ((compactTrivialization S.borel P S.iwasawa .plus s φ).val
          (S.borel.liftedW⁻¹ * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val 1 ∂μ) =
        if 3 ∣ n + 1 then (haarMass (LocalField F q) μ : ℂ) *
          (1 - (residueCardinality (LocalField F q) : ℂ)⁻¹) * (t (LocalField F q) s) ^ ((n + 1) / 3) else 0) :
    ∀ s : ℂ, convergenceHalfPlane .plus s →
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ .plus s φ 1 1 = forwardFactor (LocalField F q) μ s := by
  intro s hs
  let integrand : (LocalField F q) → ℂ := fun x => ((compactTrivialization S.borel P S.iwasawa .plus s φ).val
    (S.borel.liftedW⁻¹ * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val 1
  have hi : Integrable integrand μ := by
    have hi := DedekindZetaZeroFree.KPRankOneActualShellCaller.integral_integrable_at_level
      F ζ hζ q S P μ hμ S.iwasawa.compact le_rfl .plus s hs
      ⟨φ, spherical_vector_mem_level (LocalField F q) S.borel P S.iwasawa .plus φ hφ⟩ (1 : ActualCover F ζ hζ q) (1 : actualTorus F ζ hζ q)
    simp only [sourceSign, id_eq, sourceParameter, if_pos rfl, kernelW, mul_one] at hi
    exact hi
  have hr : ‖t (LocalField F q) s‖ < 1 := by
    simpa using (convergence_iff_geometric (LocalField F q) .plus s).mp hs
  have he := integral_of_geometric_cubic_shells (LocalField F q) μ integrand (haarMass (LocalField F q) μ : ℂ)
    (residueCardinality (LocalField F q) : ℂ)⁻¹ (t (LocalField F q) s) hr hi (hBall s hs) (fun n => by
      rw [hShell s hs n]
      split_ifs <;> ring)
  change (∫ x, _ ∂μ) = _
  simp only [sourceSign, sourceParameter, if_pos rfl, kernelW, mul_one]
  change (∫ x, integrand x ∂μ) = _
  rw [he]
  unfold forwardFactor forwardFactorInRoot t
  ring

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
