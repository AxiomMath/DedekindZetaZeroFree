module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.BruhatSupportUniformizerClasses
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TameStableWhittakerIntegrals
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ScalarSectionLiftsAndWhittakerDimension

@[expose] public section

section
noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests

theorem basis_of_delta_tests
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (W : Submodule K (V →ₗ[K] K)) (L : ι → W) (test : ι → V)
    (v : K) (hv : v ≠ 0)
    (hpair : ∀ i j, (L i).val (test j) = v * if i = j then 1 else 0)
    [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ Fintype.card ι) :
    ∃ b : Module.Basis ι K W, ∀ i, b i = L i := by

  have hli : LinearIndependent K L := by
    refine (Fintype.linearIndependent_iff (v := L)).mpr ?_
    intro g hg j
    have h := congrArg (fun w : W => (LinearMap.applyₗ (test j)) w.val) hg
    simp only [map_sum, map_smul, map_zero, Submodule.coe_sum, Submodule.coe_smul,
      LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.applyₗ_apply_apply] at h
    rw [Finset.sum_eq_single j] at h
    · rw [hpair, if_pos rfl, mul_one, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hv
    · intro b _ hbj
      simp [hpair, if_neg hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

  have hcard : Fintype.card ι = Module.finrank K W :=
    le_antisymm (LinearIndependent.fintype_card_le_finrank hli) hdim
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' (K := K) L hli hcard, fun i => by simp⟩

end DedekindZetaZeroFree.KPTameJacquetBruhatTests

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatRootRestriction

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem root_restriction_and_mass
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (m : ℕ) (K : OpenSubgroup (ActualCover F ζ hζ q))
    (hK : (K : Set (ActualCover F ζ hζ q)) = splitCongruenceSet F ζ hζ q m)
    (hweyl : ∀ k : ActualCover F ζ hζ q,
      k ∈ K ↔ KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ K)
    (hcompact : IsCompact (rootLevelSet F ζ hζ q m))
    (hopen : IsOpen (rootLevelSet F ζ hζ q m))
    (hzero : (0 : LocalField F q) ∈ rootLevelSet F ζ hζ q m)
    (hints : rootLevelSet F ζ hζ q m ⊆ (valuation (LocalField F q)).integer)
    (hcell : ∀ (i j : Fin 3) (x : LocalField F q),
      eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈
          bruhatSupport F ζ hζ q S P π j m ↔
        i = j ∧ x ∈ rootLevelSet F ζ hζ q m)
    (test : Fin 3 → scalarSections F ζ hζ q S P hP ε)
    (hsupport : ∀ j, Function.support (test j).val ⊆ bruhatSupport F ζ hζ q S P π j m)
    (hnormalized : ∀ (j : Fin 3) (k : ActualCover F ζ hζ q),
      k ∈ splitCongruenceSet F ζ hζ q m →
        (test j).val (eta F ζ hζ q π j * k *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1) :
    MeasurableSet (rootLevelSet F ζ hζ q m) ∧
    μ (rootLevelSet F ζ hζ q m) ≠ ⊤ ∧ 0 < rootMass F ζ hζ q μ m ∧
    (∃ r₀ : ℕ, ∀ r ≥ r₀, rootLevelSet F ζ hζ q m ⊆ expandingBall F q π r) ∧
    (∀ (i j : Fin 3) (x : LocalField F q),
      (test j).val (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) =
          (rootLevelSet F ζ hζ q m).indicator (fun _ => if i = j then 1 else 0) x) := by
  have hfinite : μ (rootLevelSet F ζ hζ q m) ≠ ⊤ := hcompact.measure_ne_top
  have hpositive : 0 < rootMass F ζ hζ q μ m := by
    exact ENNReal.toReal_pos (hopen.measure_pos μ ⟨0, hzero⟩).ne' hfinite
  have hπint : (π : LocalField F q) ∈ (valuation (LocalField F q)).integer := by
    rw [Valuation.mem_integer_iff]
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q)).toOrderIso.le_iff_le.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) ≤
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  refine ⟨hopen.measurableSet, hfinite, hpositive, ⟨0, ?_⟩, ?_⟩
  · intro r hr x hx
    refine ⟨⟨(π : LocalField F q) ^ r * x,
      (valuation (LocalField F q)).integer.mul_mem
        ((valuation (LocalField F q)).integer.pow_mem hπint r) (hints hx)⟩, ?_⟩
    change x = ((π : LocalField F q) ^ r)⁻¹ * ((π : LocalField F q) ^ r * x)
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ π.ne_zero), one_mul]
  · intro i j x
    by_cases hx : x ∈ rootLevelSet F ζ hζ q m
    · by_cases hij : i = j
      · subst i
        have hn : KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈ K := by
          change KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈
            (K : Set (ActualCover F ζ hζ q))
          rw [hK]
          exact hx
        have hk := (hweyl _).mp hn
        change KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x *
          (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈
          (K : Set (ActualCover F ζ hζ q)) at hk
        rw [hK] at hk
        have hv := hnormalized j
          (KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x *
            (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹) hk
        simpa only [mul_assoc, inv_mul_cancel, mul_one, Set.indicator_of_mem hx,
          if_true] using hv
      · have hnot : eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∉
            bruhatSupport F ζ hζ q S P π j m := by
          rw [hcell]
          exact fun h => hij h.1
        have hz := Function.notMem_support.mp (fun h => hnot (hsupport j h))
        simpa only [Set.indicator_of_mem hx, if_neg hij] using hz
    · have hnot : eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∉
          bruhatSupport F ζ hζ q S P π j m := by
        rw [hcell]
        exact fun h => hx h.2
      have hz := Function.notMem_support.mp (fun h => hnot (hsupport j h))
      simpa only [Set.indicator_of_notMem hx] using hz

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatRootRestriction

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatScalarTests

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

namespace ScalarConstruction

variable {G : Type*} [Group G] (B K : Subgroup G) (a : G) (χ : B →* ℂ)
 def chart (g : G) : Prop := ∃ (b : B) (k : K), g = b * a * k
 def f (g : G) : ℂ := if h : chart B K a g then χ h.choose else 0
private theorem unique (hd : ∀ b : B, a⁻¹ * (b : G) * a ∈ K → χ b = 1)
    (b c : B) (k l : K) (he : (b : G) * a * k = c * a * l) : χ b = χ c := by
  have hm : a⁻¹ * ((c⁻¹ * b : B) : G) * a ∈ K := by
    have h : a⁻¹ * ((c⁻¹ * b : B) : G) * a = (l : G) * (k : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc
        a⁻¹ * ((c : G)⁻¹ * b) * a = a⁻¹ * (c : G)⁻¹ * ((b : G) * a * k) * (k : G)⁻¹ := by group
        _ = a⁻¹ * (c : G)⁻¹ * ((c : G) * a * l) * (k : G)⁻¹ := by rw [he]
        _ = (l : G) * (k : G)⁻¹ := by group
    rw [h]
    exact K.mul_mem l.property (K.inv_mem k.property)
  have hχ := hd (c⁻¹ * b) hm
  calc
    χ b = χ (c * (c⁻¹ * b)) := by simp
    _ = χ c := by rw [map_mul, hχ, mul_one]
private theorem f_chart (hd : ∀ b : B, a⁻¹ * (b : G) * a ∈ K → χ b = 1)
    (b : B) (k : K) : f B K a χ ((b : G) * a * k) = χ b := by
  have h : chart B K a ((b : G) * a * k) := ⟨b, k, rfl⟩
  rw [f, dif_pos h]
  obtain ⟨l, hl⟩ := h.choose_spec
  exact unique B K a χ hd _ b l k hl.symm
private theorem right (hd : ∀ b : B, a⁻¹ * (b : G) * a ∈ K → χ b = 1)
    (g : G) (k : K) : f B K a χ (g * k) = f B K a χ g := by
  by_cases h : chart B K a g
  · obtain ⟨b, l, rfl⟩ := h
    simpa only [Subgroup.coe_mul, mul_assoc] using
      (f_chart B K a χ hd b (l * k)).trans (f_chart B K a χ hd b l).symm
  · have hn : ¬ chart B K a (g * k) := by
      rintro ⟨b, l, hl⟩
      apply h
      refine ⟨b, l * k⁻¹, ?_⟩
      have he : g = (g * k) * (k : G)⁻¹ := by group
      rw [he, hl]
      simp [mul_assoc]
    simp [f, dif_neg h, dif_neg hn]
private theorem covariant (hd : ∀ b : B, a⁻¹ * (b : G) * a ∈ K → χ b = 1)
    (b : B) (g : G) : f B K a χ ((b : G) * g) = χ b * f B K a χ g := by
  by_cases h : chart B K a g
  · obtain ⟨c, l, rfl⟩ := h
    rw [← mul_assoc (b : G) ((c : G) * a) (l : G),
      ← mul_assoc (b : G) (c : G) a, ← Subgroup.coe_mul,
      f_chart B K a χ hd, f_chart B K a χ hd, map_mul]
  · have hn : ¬ chart B K a ((b : G) * g) := by
      rintro ⟨c, l, hl⟩
      apply h
      refine ⟨b⁻¹ * c, l, ?_⟩
      have he : g = (b : G)⁻¹ * ((b : G) * g) := by group
      rw [he, hl]
      simp [mul_assoc]
    simp [f, dif_neg h, dif_neg hn]

end ScalarConstruction

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 def retractHom : BL F ζ hζ q S P →* HL F ζ hζ q S P where
  toFun := retractL F ζ hζ q S P
  map_one' := by
    apply Subtype.ext
    change S.borel.retract (1 : S.borel.B) = 1
    exact map_one _
  map_mul' b c := by
    apply Subtype.ext
    change S.borel.retract (inBorel F ζ hζ q S P (b * c)) = _
    have he : inBorel F ζ hζ q S P (b * c) =
        inBorel F ζ hζ q S P b * inBorel F ζ hζ q S P c := rfl
    rw [he, map_mul]
    rfl
 def chiHom (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    BL F ζ hζ q S P →* ℂ where
  toFun := chi F ζ hζ q S P hP ε
  map_one' := by
    have hr : retractL F ζ hζ q S P 1 = 1 := (retractHom F ζ hζ q S P).map_one
    cases ε <;> simp [chi, chiH, hr, normPower, localAbs_one]
  map_mul' b c := by
    have hr : retractL F ζ hζ q S P (b * c) =
        retractL F ζ hζ q S P b * retractL F ζ hζ q S P c :=
      (retractHom F ζ hζ q S P).map_mul _ _
    have hn : ∀ x y : (LocalField F q)ˣ,
        normPower (LocalField F q) (x * y) (1 / 2) =
          normPower (LocalField F q) x (1 / 2) * normPower (LocalField F q) y (1 / 2) := by
      intro x y
      simp [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ _))
        (ne_of_gt (localAbs_pos _ _)), mul_add, Complex.exp_add]
    cases ε <;> simp only [chi, chiH, hr, map_mul, Subgroup.coe_mul, Units.val_mul] <;>
      rw [hn] <;> ring
theorem scalar_characteristic_sections
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (K : OpenSubgroup (ActualCover F ζ hζ q))
    (hK : (K : Set (ActualCover F ζ hζ q)) = splitCongruenceSet F ζ hζ q m)
    (hweyl : ∀ k : ActualCover F ζ hζ q,
      k ∈ K ↔ KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ K)
    (hdescent : ∀ (j : Fin 3) (b : BL F ζ hζ q S P),
      (eta F ζ hζ q π j)⁻¹ * (b : ActualCover F ζ hζ q) *
        eta F ζ hζ q π j ∈ K → chi F ζ hζ q S P hP ε b = 1) :
    ∃ test : Fin 3 → scalarSections F ζ hζ q S P hP ε,
      (∀ j, (∀ k ∈ splitCongruenceSet F ζ hζ q m,
        scalarAction F ζ hζ q S P hP ε k (test j) = test j) ∧
        Function.support (test j).val ⊆ bruhatSupport F ζ hζ q S P π j m) ∧
      (∀ (j : Fin 3) (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
        k ∈ splitCongruenceSet F ζ hζ q m →
          (test j).val ((b : ActualCover F ζ hζ q) * eta F ζ hζ q π j * k *
            KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = chi F ζ hζ q S P hP ε b) ∧
      (∀ (j : Fin 3) (k : ActualCover F ζ hζ q),
        k ∈ splitCongruenceSet F ζ hζ q m →
          (test j).val (eta F ζ hζ q π j * k *
            KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1) := by
  let B := BL F ζ hζ q S P
  let W := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
  let χ := chiHom F ζ hζ q S P hP ε
  have conjugate (k : ActualCover F ζ hζ q) (hk : k ∈ K) : W⁻¹ * k * W ∈ K := by
    apply (hweyl (W⁻¹ * k * W)).mpr
    simpa only [W, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_inv_cancel_left, inv_mul_cancel_left, one_mul, mul_one] using hk
  have hd (j : Fin 3) (b : B)
      (hb : (eta F ζ hζ q π j * W)⁻¹ * (b : ActualCover F ζ hζ q) *
        (eta F ζ hζ q π j * W) ∈ K) : χ b = 1 := by
    apply hdescent j b
    have ht := (hweyl _).mp hb
    simpa only [W, mul_inv_rev, mul_assoc, mul_inv_cancel, inv_mul_cancel,
      mul_inv_cancel_left, inv_mul_cancel_left, one_mul, mul_one] using ht
  let f : Fin 3 → ActualCover F ζ hζ q → ℂ := fun j =>
    ScalarConstruction.f B K.toSubgroup (eta F ζ hζ q π j * W) χ
  have hright (j : Fin 3) (g : ActualCover F ζ hζ q) (k : ActualCover F ζ hζ q)
      (hk : k ∈ K) : f j (g * k) = f j g :=
    ScalarConstruction.right B K.toSubgroup _ χ (hd j) g ⟨k, hk⟩
  have hcov (j : Fin 3) (b : B) (g : ActualCover F ζ hζ q) :
      f j ((b : ActualCover F ζ hζ q) * g) = chi F ζ hζ q S P hP ε b * f j g :=
    ScalarConstruction.covariant B K.toSubgroup _ χ (hd j) b g
  let test : Fin 3 → scalarSections F ζ hζ q S P hP ε := fun j =>
    ⟨f j, hcov j, ⟨K, fun k hk => by
      ext g
      exact hright j g k hk⟩⟩
  have heval (j : Fin 3) (b : B) (k : ActualCover F ζ hζ q)
      (hk : k ∈ splitCongruenceSet F ζ hζ q m) :
      (test j).val ((b : ActualCover F ζ hζ q) * eta F ζ hζ q π j * k * W) =
        chi F ζ hζ q S P hP ε b := by
    have hkK : k ∈ K := by change k ∈ (K : Set _); rw [hK]; exact hk
    have ht := ScalarConstruction.f_chart B K.toSubgroup (eta F ζ hζ q π j * W) χ
      (hd j) b ⟨W⁻¹ * k * W, conjugate k hkK⟩
    change f j _ = χ b
    have he : (b : ActualCover F ζ hζ q) * eta F ζ hζ q π j * k * W =
        (b : ActualCover F ζ hζ q) * (eta F ζ hζ q π j * W) * (W⁻¹ * k * W) := by group
    rw [he]
    exact ht
  refine ⟨test, ?_, heval, ?_⟩
  · intro j
    constructor
    · intro k hk
      apply Subtype.ext
      ext g
      exact hright j g k (by change k ∈ (K : Set _); rw [hK]; exact hk)
    · intro g hg
      change f j g ≠ 0 at hg
      have hc : ScalarConstruction.chart B K.toSubgroup (eta F ζ hζ q π j * W) g := by
        by_contra hn
        exact hg (by simp [f, ScalarConstruction.f, hn])
      obtain ⟨b, k, hk⟩ := hc
      refine ⟨b, W * (k : ActualCover F ζ hζ q) * W⁻¹, ?_, ?_⟩
      · rw [← hK]
        exact (hweyl _).mp k.property
      · change g = (b : ActualCover F ζ hζ q) * eta F ζ hζ q π j * (W * (k : ActualCover F ζ hζ q) * W⁻¹) * W
        rw [hk]
        group
  · intro j k hk
    have ht := heval j (1 : B) k hk
    have hone : chi F ζ hζ q S P hP ε (1 : B) = 1 := χ.map_one
    simpa only [Subgroup.coe_one, one_mul, hone] using ht

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatScalarTests

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

namespace TestConstruction

theorem eventually_matrixChartDepth :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, KPLocalChartTopology.MatrixChartDepth F q m := by
  obtain ⟨m₀, hm₀, _, _, hcharts⟩ :=
    KPLocalCube.deep_principal_units_and_matrix_charts F q
  refine ⟨m₀, fun m hm => ⟨hm₀.trans hm, ?_⟩⟩
  exact (hcharts m hm).2.2

 theorem stableValue_of_indicator
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (m : ℕ) (c : ℂ)
    (hs : MeasurableSet (rootLevelSet F ζ hζ q m))
    (hfinite : μ (rootLevelSet F ζ hζ q m) ≠ ⊤)
    (hball : ∃ r₀ : ℕ, ∀ r ≥ r₀, rootLevelSet F ζ hζ q m ⊆ expandingBall F q π r)
    (hvalue : jacquetIntegrand F ζ hζ q S P hP ε ψ a f =
      (rootLevelSet F ζ hζ q m).indicator (fun _ => c)) :
    HasStableValue F ζ hζ q S P hP ε π ψ μ a f
      ((rootMass F ζ hζ q μ m : ℂ) * c) := by
  obtain ⟨r₀, hr₀⟩ := hball
  refine ⟨r₀, ?_⟩
  intro r hr
  rw [hvalue]
  have hi : Integrable ((rootLevelSet F ζ hζ q m).indicator (fun _ => c)) μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hfinite)
  refine ⟨hi.integrableOn, ?_⟩
  rw [integral_indicator hs, Measure.restrict_restrict_of_subset (hr₀ r hr)]
  simp [rootMass, integral_const, smul_eq_mul, Measure.real]
theorem conductor_trivial_on_integers
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hc : HasConductorIntegers F q ψ)
    {x : LocalField F q} (hx : x ∈ (valuation (LocalField F q)).integer) :
    ψ (Multiplicative.ofAdd (-x)) = 1 := by
  have hn := ((valuation (LocalField F q)).integer).neg_mem hx
  have hh := (hc (-x)).mpr hn (1 : 𝒪[LocalField F q])
  simpa using hh

theorem stable_delta_of_root_restriction
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hc : HasConductorIntegers F q ψ)
    (μ : Measure (LocalField F q))
    (test : Fin 3 → scalarSections F ζ hζ q S P hP ε) (m : ℕ)
    (hs : MeasurableSet (rootLevelSet F ζ hζ q m))
    (hfinite : μ (rootLevelSet F ζ hζ q m) ≠ ⊤)
    (hints : rootLevelSet F ζ hζ q m ⊆ (valuation (LocalField F q)).integer)
    (hball : ∃ r₀ : ℕ, ∀ r ≥ r₀, rootLevelSet F ζ hζ q m ⊆ expandingBall F q π r)
    (hrestriction : ∀ i j x,
      (test j).val (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) =
          (rootLevelSet F ζ hζ q m).indicator (fun _ => if i = j then 1 else 0) x) :
    ∀ i j, HasStableValue F ζ hζ q S P hP ε π ψ μ
      (eta F ζ hζ q π i) (test j)
      ((rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0) := by
  intro i j
  apply stableValue_of_indicator F ζ hζ q S P hP ε π ψ μ
    (eta F ζ hζ q π i) (test j) m (if i = j then 1 else 0) hs hfinite hball
  funext x
  simp only [jacquetIntegrand.eq_1, hrestriction]
  by_cases hx : x ∈ rootLevelSet F ζ hζ q m
  · rw [Set.indicator_of_mem hx,
      conductor_trivial_on_integers F q ψ hc (hints hx)]
    simp
  · simp [Set.indicator_of_notMem hx]

end TestConstruction

theorem compact_bruhat_tests
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hψ : Continuous ψ) (hunitary : ∀ x, ‖(ψ x : ℂ)‖ = 1)
    (hconductor : HasConductorIntegers F q ψ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ε : Sign) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      KPLocalChartTopology.MatrixChartDepth F q m ∧
      μ (rootLevelSet F ζ hζ q m) ≠ ⊤ ∧ 0 < rootMass F ζ hζ q μ m ∧
      ∃ test : Fin 3 → scalarSections F ζ hζ q S P hP ε,
        (∀ j, (∀ k ∈ splitCongruenceSet F ζ hζ q m,
          scalarAction F ζ hζ q S P hP ε k (test j) = test j) ∧
          Function.support (test j).val ⊆ bruhatSupport F ζ hζ q S P π j m ∧
          (test j).val (eta F ζ hζ q π j *
            KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1) ∧
        (∀ i j, HasStableValue F ζ hζ q S P hP ε π ψ μ
          (eta F ζ hζ q π i) (test j)
          ((rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0)) := by
  obtain ⟨mchart, hchart⟩ := TestConstruction.eventually_matrixChartDepth F q
  obtain ⟨mgeom, hgeom⟩ :=
    BruhatGeometry.eventually_actual_raw_bruhat_geometry F ζ hζ q S P
      hP htame π hπ ε
  refine ⟨max mchart mgeom, ?_⟩
  intro m hm
  obtain ⟨K, hK, _hcompactK, hweyl, hdescent, hcompact, hopen, hzero, hints, hcell⟩ :=
    hgeom m ((le_max_right _ _).trans hm)
  obtain ⟨test, htest, _hcharacteristic, hnormalized⟩ :=
    BruhatScalarTests.scalar_characteristic_sections F ζ hζ q S P
      hP ε π m K hK hweyl hdescent
  obtain ⟨hs, hfinite, hpositive, hball, hrestriction⟩ :=
    BruhatRootRestriction.root_restriction_and_mass F ζ hζ q S P
      hP ε π hπ μ m K hK hweyl hcompact hopen hzero hints hcell
      test (fun j => (htest j).2) hnormalized
  refine ⟨hchart m ((le_max_left _ _).trans hm), hfinite, hpositive,
    test, ?_, ?_⟩
  · intro j
    refine ⟨(htest j).1, (htest j).2, ?_⟩
    have hone : (1 : ActualCover F ζ hζ q) ∈ splitCongruenceSet F ζ hζ q m := by
      rw [← hK]
      exact K.one_mem
    simpa using hnormalized j 1 hone
  · exact TestConstruction.stable_delta_of_root_restriction F ζ hζ q S P
      hP ε π ψ hconductor μ test m hs hfinite hints hball hrestriction

end DedekindZetaZeroFree.KPTameJacquetBruhatTests

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPTameJacquetTestDuality

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

abbrev HL : Subgroup (actualTorus F ζ hζ q) := P.L.comap S.heisenberg.π

def IsTamePolarization : Prop :=
  P.L.map S.cubeClassEquiv.toMonoidHom =
    KPTameValuationCoordinates.unitCubeClasses (LocalField F q)

private theorem pgl_diagonal_injective (K : Type*) [Field K] (u v : Kˣ)
    (huv : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u 1) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K v 1)) : u = v := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp huv
  have h11 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hc
  have h00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply] at h11 h00
  apply Units.ext
  calc
    (u : K) = (u : K) * (c : K) := by simp [h11]
    _ = (v : K) := h00

private theorem pgl_weyl_diagonal (K : Type*) [Field K] (u : Kˣ) :
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u⁻¹ 1) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u 1) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K) := by
  rw [← map_mul, ← map_mul]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal_apply]

private theorem weyl_coordinate (h : actualTorus F ζ hζ q) :
    S.borel.coordinate (S.borel.weyl h) = (S.borel.coordinate h)⁻¹ := by
  apply pgl_diagonal_injective
  rw [← S.borel.torus_projection]
  rw [S.borel.weyl_from_lift, map_mul, map_mul, map_inv, S.borel.liftedW_projection,
    S.borel.torus_projection]
  apply mul_left_cancel (a := Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)))
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact (pgl_weyl_diagonal (LocalField F q) (S.borel.coordinate h)).symm

theorem weyl_preserves_HL (hP : IsTamePolarization F ζ hζ q S P)
    (h : HL F ζ hζ q S P) :
    S.borel.weyl (h : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
  have hm : S.cubeClassEquiv (S.heisenberg.π (h : actualTorus F ζ hζ q)) ∈
      KPTameValuationCoordinates.unitCubeClasses (LocalField F q) := by
    rw [← hP]
    exact ⟨S.heisenberg.π h, h.property, rfl⟩
  have hw : S.cubeClassEquiv (S.heisenberg.π (S.borel.weyl h)) =
      (S.cubeClassEquiv (S.heisenberg.π (h : actualTorus F ζ hζ q)))⁻¹ := by
    rw [S.cube_class, S.cube_class, weyl_coordinate F ζ hζ q S]
    exact map_inv (QuotientGroup.mk' _) _
  change S.heisenberg.π (S.borel.weyl h) ∈ P.L
  have hi := (KPTameValuationCoordinates.unitCubeClasses (LocalField F q)).inv_mem hm
  rw [← hw, ← hP] at hi
  obtain ⟨d, hd, he⟩ := hi
  exact S.cubeClassEquiv.injective he ▸ hd

def weylHL (hP : IsTamePolarization F ζ hζ q S P) :
    HL F ζ hζ q S P →* HL F ζ hζ q S P where
  toFun h := ⟨S.borel.weyl h, weyl_preserves_HL F ζ hζ q S P hP h⟩
  map_one' := Subtype.ext (map_one S.borel.weyl)
  map_mul' x y := Subtype.ext (map_mul S.borel.weyl
    (x : actualTorus F ζ hζ q) (y : actualTorus F ζ hζ q))

def BL : Subgroup (ActualCover F ζ hζ q) :=
  ((HL F ζ hζ q S P).comap S.borel.retract).map S.borel.B.subtype

def inBorel (b : BL F ζ hζ q S P) : S.borel.B :=
  ⟨b, by
    obtain ⟨a, _, ha⟩ := b.property
    exact ha ▸ a.property⟩

def retractL (b : BL F ζ hζ q S P) : HL F ζ hζ q S P :=
  ⟨S.borel.retract (inBorel F ζ hζ q S P b), by
    obtain ⟨a, ha, he⟩ := b.property
    have he' : inBorel F ζ hζ q S P b = a := Subtype.ext he.symm
    rw [he']
    exact ha⟩

def chiH (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (h : HL F ζ hζ q S P) : ℂ :=
  (match ε with
    | .plus => (P.ωL h : ℂ)
    | .minus => (P.ωL (weylHL F ζ hζ q S P hP h) : ℂ)) *
    normPower (LocalField F q) (S.borel.coordinate h) (1 / 2)

def chi (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (b : BL F ζ hζ q S P) : ℂ :=
  chiH F ζ hζ q S P hP ε (retractL F ζ hζ q S P b)

def scalarSections (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    Submodule ℂ (ActualCover F ζ hζ q → ℂ) where
  carrier := {f | (∀ (b : BL F ζ hζ q S P) (g : ActualCover F ζ hζ q),
    f ((b : ActualCover F ζ hζ q) * g) = chi F ζ hζ q S P hP ε b * f g) ∧
    SmoothVector rightTranslationRepresentation f}
  zero_mem' := ⟨by intros; simp, ⟨⊤, by intros; simp⟩⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).add_mem
      ((mem_smoothSubmodule _ _).mpr hf.2) ((mem_smoothSubmodule _ _).mpr hg.2))⟩
    intro b x
    simp only [Pi.add_apply, hf.1, hg.1, mul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨?_, (mem_smoothSubmodule _ _).mp ((smoothSubmodule _).smul_mem c
      ((mem_smoothSubmodule _ _).mpr hf.2))⟩
    intro b x
    simp only [Pi.smul_apply, smul_eq_mul, hf.1]
    ring

 theorem scalarSections_stable
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) (g : ActualCover F ζ hζ q) :
    scalarSections F ζ hζ q S P hP ε ≤
      (scalarSections F ζ hζ q S P hP ε).comap (rightTranslationRepresentation g) := by
  intro f hf
  refine ⟨?_, (mem_smoothSubmodule _ _).mp (smoothSubmodule_stable _ g
    ((mem_smoothSubmodule _ _).mpr hf.2))⟩
  intro b x
  change f (((b : ActualCover F ζ hζ q) * x) * g) = _
  rw [mul_assoc, hf.1]
  rfl

def scalarAction (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    Representation ℂ (ActualCover F ζ hζ q) (scalarSections F ζ hζ q S P hP ε) :=
  rightTranslationRepresentation.subrepresentation _
    (scalarSections_stable F ζ hζ q S P hP ε)

def eta (π : (LocalField F q)ˣ) (j : Fin 3) : ActualCover F ζ hζ q :=
  KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ j.val)

def expandingBall (π : (LocalField F q)ˣ) (r : ℕ) : Set (LocalField F q) :=
  {x | ∃ o : 𝒪[LocalField F q], x = ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹ * o}

def jacquetIntegrand (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (x : LocalField F q) : ℂ :=
  f.val (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) *
    (ψ (Multiplicative.ofAdd (-x)) : ℂ)

def HasStableValue (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (z : ℂ) : Prop :=
  ∃ r₀ : ℕ, ∀ r ≥ r₀,
    IntegrableOn (jacquetIntegrand F ζ hζ q S P hP ε ψ a f)
      (expandingBall F q π r) μ ∧
    (∫ x in expandingBall F q π r,
      jacquetIntegrand F ζ hζ q S P hP ε ψ a f x ∂μ) = z

theorem stable_value_unique
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) {z z' : ℂ}
    (hz : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z)
    (hz' : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z') : z = z' := by
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r', hr'⟩ := hz'
  exact (hr (max r r') (le_max_left _ _)).2.symm.trans
    (hr' (max r r') (le_max_right _ _)).2

def HasConductorIntegers (ψ : Multiplicative (LocalField F q) →* ℂˣ) : Prop :=
  ∀ y : LocalField F q,
    (∀ x : 𝒪[LocalField F q], ψ (Multiplicative.ofAdd ((x : LocalField F q) * y)) = 1) ↔
      y ∈ (valuation (LocalField F q)).integer

def splitCongruenceSet (m : ℕ) : Set (ActualCover F ζ hζ q) :=
  Set.range (fun k : KPLocalCube.Gamma F q m =>
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val))

def rootLevelSet (m : ℕ) : Set (LocalField F q) :=
  {x | KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈ splitCongruenceSet F ζ hζ q m}

def rootMass (μ : Measure (LocalField F q)) (m : ℕ) : ℝ :=
  (μ (rootLevelSet F ζ hζ q m)).toReal

def bruhatSupport (π : (LocalField F q)ˣ) (j : Fin 3) (m : ℕ) :
    Set (ActualCover F ζ hζ q) :=
  {g | ∃ (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
    k ∈ splitCongruenceSet F ζ hζ q m ∧
      g = b * eta F ζ hζ q π j * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)}

abbrev whittakerSpace (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) :=
  algebraicWhittaker (scalarAction F ζ hζ q S P hP ε)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ

abbrev Jacquet (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) :=
  RootCoinvariants (scalarAction F ζ hζ q S P hP ε)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ

def descend (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (L : whittakerSpace F ζ hζ q S P hP ε ψ) :
    Jacquet F ζ hζ q S P hP ε ψ →ₗ[ℂ] ℂ :=
  rootCoinvariantsLift (scalarAction F ζ hζ q S P hP ε)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ
    ⟨L.val, by
      intro t f
      simpa only [smul_eq_mul] using L.property t f⟩

def jacquetDualEquiv (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) :
    (Jacquet F ζ hζ q S P hP ε ψ →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      whittakerSpace F ζ hζ q S P hP ε ψ := by
  let e : RootEquivariantMaps (scalarAction F ζ hζ q S P hP ε)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ ℂ ≃ₗ[ℂ]
      whittakerSpace F ζ hζ q S P hP ε ψ :=
    { toFun := fun L => ⟨L.val, by
        intro t f
        simpa only [smul_eq_mul] using L.property t f⟩
      invFun := fun L => ⟨L.val, by
        intro t f
        simpa only [smul_eq_mul] using L.property t f⟩
      left_inv := by intro L; rfl
      right_inv := by intro L; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (rootCoinvariantsUniversalEquiv (scalarAction F ζ hζ q S P hP ε)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ ℂ).trans e

@[simp] theorem descend_mk
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (L : whittakerSpace F ζ hζ q S P hP ε ψ)
    (f : scalarSections F ζ hζ q S P hP ε) :
    descend F ζ hζ q S P hP ε ψ L
      (rootCoinvariantsMk (scalarAction F ζ hζ q S P hP ε)
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ f) = L.val f := by
  exact rootCoinvariantsLift_mk _ _ _ _ _

theorem descend_basis_separates
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (Λ : Module.Basis (Fin 3) ℂ (whittakerSpace F ζ hζ q S P hP ε ψ))
    {x y : Jacquet F ζ hζ q S P hP ε ψ}
    (hxy : ∀ i, descend F ζ hζ q S P hP ε ψ (Λ i) x =
      descend F ζ hζ q S P hP ε ψ (Λ i) y) : x = y := by
  let b := Λ.map (jacquetDualEquiv F ζ hζ q S P hP ε ψ).symm
  have he : Module.Dual.eval ℂ _ x = Module.Dual.eval ℂ _ y := by
    apply b.ext
    exact hxy
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (x - y)).mp
  intro φ
  have hφ := LinearMap.congr_fun he φ
  simpa using sub_eq_zero.mpr hφ

theorem normalized_test_dual_basis
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (Λ : Module.Basis (Fin 3) ℂ (whittakerSpace F ζ hζ q S P hP ε ψ))
    (v : ℂ) (hv : v ≠ 0)
    (test : Fin 3 → scalarSections F ζ hζ q S P hP ε)
    (hpair : ∀ i j, (Λ i).val (test j) = v * if i = j then 1 else 0) :
    ∃ dual : Module.Basis (Fin 3) ℂ (Jacquet F ζ hζ q S P hP ε ψ),
      (∀ j, dual j = rootCoinvariantsMk (scalarAction F ζ hζ q S P hP ε)
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ (v⁻¹ • test j)) ∧
      (∀ i j, descend F ζ hζ q S P hP ε ψ (Λ i) (dual j) =
        if i = j then 1 else 0) := by
  let e : Fin 3 → Jacquet F ζ hζ q S P hP ε ψ := fun j =>
    rootCoinvariantsMk (scalarAction F ζ hζ q S P hP ε)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ (v⁻¹ • test j)
  let d : Fin 3 → Module.Dual ℂ (Jacquet F ζ hζ q S P hP ε ψ) :=
    fun i => descend F ζ hζ q S P hP ε ψ (Λ i)
  have hd : ∀ i j, d i (e j) = if i = j then 1 else 0 := by
    intro i j
    simp only [d, e, descend_mk, map_smul, smul_eq_mul, hpair]
    rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
  have hdual : Module.DualBases e d :=
    { eval_same := fun i => by simpa using hd i i
      eval_of_ne := fun i j hij => by simpa [hij] using hd i j
      total := fun h => descend_basis_separates F ζ hζ q S P hP ε ψ Λ h }
  refine ⟨hdual.basis, ?_, ?_⟩
  · intro j
    exact congrFun hdual.coe_basis j
  · intro i j
    change d i (hdual.basis j) = _
    rw [show hdual.basis j = e j from congrFun hdual.coe_basis j]
    exact hd i j

theorem stable_value_torus_covariance
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (h : HL F ζ hζ q S P)
    (a : ActualCover F ζ hζ q) (f : scalarSections F ζ hζ q S P hP ε) (z : ℂ)
    (hz : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z) :
    HasStableValue F ζ hζ q S P hP ε π ψ μ
      ((S.borel.torus h : ActualCover F ζ hζ q) * a) f
      (chiH F ζ hζ q S P hP ε h * z) := by
  let b : BL F ζ hζ q S P :=
    ⟨(S.borel.torus h : ActualCover F ζ hζ q),
      ⟨S.borel.torus h, by
        change S.borel.retract (S.borel.torus h) ∈ HL F ζ hζ q S P
        rw [S.borel.retract_torus]
        exact h.property, rfl⟩⟩
  have hb : retractL F ζ hζ q S P b = h := by
    apply Subtype.ext
    change S.borel.retract (inBorel F ζ hζ q S P b) = h
    have hi : inBorel F ζ hζ q S P b = S.borel.torus h := Subtype.ext rfl
    rw [hi, S.borel.retract_torus]
  have he : jacquetIntegrand F ζ hζ q S P hP ε ψ
      ((S.borel.torus h : ActualCover F ζ hζ q) * a) f =
      fun x => chiH F ζ hζ q S P hP ε h *
        jacquetIntegrand F ζ hζ q S P hP ε ψ a f x := by
    funext x
    dsimp only [jacquetIntegrand]
    rw [mul_assoc (S.borel.torus h : ActualCover F ζ hζ q),
      mul_assoc (S.borel.torus h : ActualCover F ζ hζ q)]
    rw [show f.val ((S.borel.torus h : ActualCover F ζ hζ q) *
        (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) =
        chi F ζ hζ q S P hP ε b * f.val
        (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) from f.property.1 b _]
    rw [chi, hb, mul_assoc]
  obtain ⟨r₀, hr⟩ := hz
  refine ⟨r₀, ?_⟩
  intro r hrr
  obtain ⟨hint, hval⟩ := hr r hrr
  rw [he]
  exact ⟨hint.const_mul _, by rw [integral_const_mul, hval]⟩

def TameJacquetTestDualityOutput
    (hP : IsTamePolarization F ζ hζ q S P) (π : (LocalField F q)ˣ)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (μ : Measure (LocalField F q)) : Prop :=
  ∀ ε : Sign, ∃ Λ : Module.Basis (Fin 3) ℂ (whittakerSpace F ζ hζ q S P hP ε ψ),
    (∀ j f, HasStableValue F ζ hζ q S P hP ε π ψ μ
      (eta F ζ hζ q π j) f ((Λ j).val f)) ∧
    (∀ (h : HL F ζ hζ q S P) (a : ActualCover F ζ hζ q)
      (f : scalarSections F ζ hζ q S P hP ε) (z : ℂ),
      HasStableValue F ζ hζ q S P hP ε π ψ μ a f z →
      HasStableValue F ζ hζ q S P hP ε π ψ μ
        ((S.borel.torus h : ActualCover F ζ hζ q) * a) f
        (chiH F ζ hζ q S P hP ε h * z)) ∧
    (∃ m₀ : ℕ, ∀ m ≥ m₀,
      KPLocalChartTopology.MatrixChartDepth F q m ∧
      μ (rootLevelSet F ζ hζ q m) ≠ ⊤ ∧ 0 < rootMass F ζ hζ q μ m ∧
      ∃ test : Fin 3 → scalarSections F ζ hζ q S P hP ε,
        (∀ j, (∀ k ∈ splitCongruenceSet F ζ hζ q m,
          scalarAction F ζ hζ q S P hP ε k (test j) = test j) ∧
          Function.support (test j).val ⊆ bruhatSupport F ζ hζ q S P π j m ∧
          (test j).val (eta F ζ hζ q π j * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1) ∧
        (∀ i j, (Λ i).val (test j) =
          (rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0) ∧
        ∃ dual : Module.Basis (Fin 3) ℂ (Jacquet F ζ hζ q S P hP ε ψ),
          (∀ j, dual j = rootCoinvariantsMk (scalarAction F ζ hζ q S P hP ε)
            (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ
            ((rootMass F ζ hζ q μ m : ℂ)⁻¹ • test j)) ∧
          (∀ i j, descend F ζ hζ q S P hP ε ψ (Λ i) (dual j) =
            if i = j then 1 else 0))

theorem tame_jacquet_test_duality
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hψ : Continuous ψ) (hunitary : ∀ x, ‖(ψ x : ℂ)‖ = 1)
    (hconductor : HasConductorIntegers F q ψ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    TameJacquetTestDualityOutput F ζ hζ q S P hP π ψ μ := by
  intro ε
  have hL := KPTameJacquetBruhatTests.stable_whittaker_family
    F ζ hζ q S P hP htame π hπ ψ hψ hunitary hconductor μ hμ ε
  change ∃ L : Fin 3 → whittakerSpace F ζ hζ q S P hP ε ψ,
    ∀ j f, HasStableValue F ζ hζ q S P hP ε π ψ μ
      (eta F ζ hζ q π j) f ((L j).val f) at hL
  obtain ⟨L, hstable⟩ := hL
  have htests := KPTameJacquetBruhatTests.compact_bruhat_tests
    F ζ hζ q S P hP htame π hπ ψ hψ hunitary hconductor μ hμ ε
  change ∃ m₀ : ℕ, ∀ m ≥ m₀,
    KPLocalChartTopology.MatrixChartDepth F q m ∧
    μ (rootLevelSet F ζ hζ q m) ≠ ⊤ ∧ 0 < rootMass F ζ hζ q μ m ∧
    ∃ test : Fin 3 → scalarSections F ζ hζ q S P hP ε,
      (∀ j, (∀ k ∈ splitCongruenceSet F ζ hζ q m,
        scalarAction F ζ hζ q S P hP ε k (test j) = test j) ∧
        Function.support (test j).val ⊆ bruhatSupport F ζ hζ q S P π j m ∧
        (test j).val (eta F ζ hζ q π j *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1) ∧
      (∀ i j, HasStableValue F ζ hζ q S P hP ε π ψ μ
        (eta F ζ hζ q π i) (test j)
        ((rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0)) at htests
  obtain ⟨m₀, htests⟩ := htests
  have hpair : ∀ m ≥ m₀, ∀ test : Fin 3 → scalarSections F ζ hζ q S P hP ε,
      (∀ i j, HasStableValue F ζ hζ q S P hP ε π ψ μ
        (eta F ζ hζ q π i) (test j)
        ((rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0)) →
      ∀ i j, (L i).val (test j) =
        (rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0 := by
    intro m hm test hv i j
    exact stable_value_unique F ζ hζ q S P hP ε π ψ μ _ _
      (hstable i (test j)) (hv i j)
  have hdim := KPTameJacquetBruhatTests.whittaker_dimension_bound
    F ζ hζ q S P hP htame ψ hψ hunitary hconductor ε
  change FiniteDimensional ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ∧
    Module.finrank ℂ (whittakerSpace F ζ hζ q S P hP ε ψ) ≤ 3 at hdim
  letI := hdim.1
  obtain ⟨_, _, hpos, test, _, hv⟩ := htests m₀ le_rfl
  have hnonzero : (rootMass F ζ hζ q μ m₀ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  obtain ⟨Λ, hΛ⟩ := KPTameJacquetBruhatTests.basis_of_delta_tests
    (algebraicWhittaker (scalarAction F ζ hζ q S P hP ε)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) ψ)
    L test (rootMass F ζ hζ q μ m₀ : ℂ) hnonzero
    (by intro i j; simpa using hpair m₀ le_rfl test hv i j)
    (by simpa using hdim.2)
  refine ⟨Λ, ?_, ?_, m₀, ?_⟩
  · intro j f
    rw [hΛ]
    exact hstable j f
  · intro h a f z hz
    exact stable_value_torus_covariance F ζ hζ q S P hP ε π ψ μ h a f z hz
  · intro m hm
    obtain ⟨hdepth, hfinite, hpositive, test, hsupport, hvalues⟩ := htests m hm
    have hp : ∀ i j, (Λ i).val (test j) =
        (rootMass F ζ hζ q μ m : ℂ) * if i = j then 1 else 0 := by
      intro i j
      rw [hΛ]
      exact hpair m hm test hvalues i j
    refine ⟨hdepth, hfinite, hpositive, test, hsupport, hp, ?_⟩
    apply normalized_test_dual_basis F ζ hζ q S P hP ε ψ Λ
      (rootMass F ζ hζ q μ m : ℂ) _ test hp
    exact_mod_cast ne_of_gt hpositive

end DedekindZetaZeroFree.KPTameJacquetTestDuality

end

end
