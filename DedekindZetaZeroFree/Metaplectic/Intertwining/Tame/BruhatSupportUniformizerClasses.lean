module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TamePolarizationsAndTwistedCoinvariants

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

 def vm (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative (ZMod 3) where
  toFun y := Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K y : ZMod 3)
  map_one' := by simp [KPCubicExpansion.valuationExponent]
  map_mul' y z := by
    change (KPCubicExpansion.valuationExponent K (y*z) : ZMod 3) = _ + _
    change (KPCubicExpansion.valuationExponent K (y*z) : ZMod 3) =
      (KPCubicExpansion.valuationExponent K y : ZMod 3) +
      (KPCubicExpansion.valuationExponent K z : ZMod 3)
    rw [KPCubicExpansion.valuationExponent_mul, Int.cast_add]
private lemma vm_cube (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : CubicCharacters.cubes Kˣ ≤ (vm K).ker := by
  rintro y ⟨z, rfl⟩
  change (KPCubicExpansion.valuationExponent K (z ^ 3) : ZMod 3) = 0
  rw [← zpow_natCast z 3, KPCubicExpansion.valuationExponent_zpow, Int.cast_mul]
  change (3 : ZMod 3) * _ = 0
  rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
private lemma unit_class_vm (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : Kˣ)
    (hu : QuotientGroup.mk' (CubicCharacters.cubes Kˣ) u ∈ KPTameValuationCoordinates.unitCubeClasses K) :
    (KPCubicExpansion.valuationExponent K u : ZMod 3) = 0 := by
  let φ := QuotientGroup.lift (CubicCharacters.cubes Kˣ) (vm K) (vm_cube K)
  have hh : KPTameValuationCoordinates.unitCubeClasses K ≤ φ.ker := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sup_le
    · rintro y ⟨z, rfl⟩
      change (KPCubicExpansion.valuationExponent K (KPRamifiedBeta.unitsInclusion K z) : ZMod 3) = 0
      rw [show KPRamifiedBeta.unitsInclusion K z = Units.map (𝒪[K]).subtype.toMonoidHom z from rfl,
        KPCubicExpansion.valuationExponent_unit]
      rfl
    · intro y hy
      change φ (QuotientGroup.mk' (CubicCharacters.cubes Kˣ) y) = 1
      exact vm_cube K hy
  exact hh hu

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

private lemma coord_vm (hP : IsTamePolarization F ζ hζ q S P) (b : BL F ζ hζ q S P) :
    (KPCubicExpansion.valuationExponent (LocalField F q)
      (S.borel.coordinate (retractL F ζ hζ q S P b)) : ZMod 3) = 0 := by
  apply unit_class_vm
  change QuotientGroup.mk (S.borel.coordinate (retractL F ζ hζ q S P b)) ∈ _
  rw [← S.cube_class, ← hP]
  exact ⟨S.heisenberg.π (retractL F ζ hζ q S P b),
    (retractL F ζ hζ q S P b).property, rfl⟩

set_option maxHeartbeats 1000000 in

theorem bruhat_support_index_eq
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (i j : Fin 3) (x : LocalField F q)
    (hg : eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈
        bruhatSupport F ζ hζ q S P π j m) :
    i = j := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) 1 *
        KubotaRankTwo.n (LocalField F q) t.toAdd) := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
        (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb] at hp
  have pa (l : Fin 3) : S.borel.projection (eta F ζ hζ q π l) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ l.val) 1) :=
    (S.openCell P).projection_eq _
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) x) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  rw [pa, pa, pw, pn, pk, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h10 := congrArg (fun g : GL (Fin 2) (LocalField F q) => (g : Matrix (Fin 2) (Fin 2) (LocalField F q)) 1 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
    Matrix.vecMul, dotProduct] at h10
  have hd := congrArg Matrix.GeneralLinearGroup.det hc
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  have detd (u : (LocalField F q)ˣ) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.d (LocalField F q) u 1) = u := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detn (z : LocalField F q) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.n (LocalField F q) z) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detw : Matrix.GeneralLinearGroup.det
      (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = -1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, KPStandardLocalRootLifts.weylSwap, Matrix.det_fin_two]
  rw [detd, detd, detd, detn, detn, detw] at hd
  have hd' : π ^ i.val * c ^ 2 = S.borel.coordinate (retractL F ζ hζ q S P b) *
      π ^ j.val * Matrix.GeneralLinearGroup.det k.val := by
    simpa [mul_assoc] using hd
  obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
  have hc' : c = r ^ 3 := Units.ext (h10.trans hr.symm)
  obtain ⟨d, hdv⟩ := (hm.2 k.val k.property).2
  change d ^ 3 = Matrix.GeneralLinearGroup.det k.val at hdv
  rw [hc', ← hdv] at hd'
  have hv := congrArg (vm (LocalField F q)) hd'
  simp only [map_mul, map_pow] at hv
  have vr (u : (LocalField F q)ˣ) : vm (LocalField F q) u ^ 3 = 1 := by
    have hu : u ^ 3 ∈ (vm (LocalField F q)).ker :=
      vm_cube (LocalField F q) (show u ^ 3 ∈ CubicCharacters.cubes (LocalField F q)ˣ from ⟨u, rfl⟩)
    change vm (LocalField F q) (u ^ 3) = 1 at hu
    simpa only [map_pow] using hu
  rw [vr, vr, one_pow, mul_one, mul_one] at hv
  have vb : vm (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) = 1 :=
    coord_vm F ζ hζ q S P hP b
  rw [vb, one_mul] at hv
  have vpi : vm (LocalField F q) π = Multiplicative.ofAdd (1 : ZMod 3) := by
    change (KPCubicExpansion.valuationExponent (LocalField F q) π : ZMod 3) = 1
    simp [KPCubicExpansion.valuationExponent, hπ, WithZero.log_exp]
  rw [vpi] at hv
  have hij : (i.val : ZMod 3) = (j.val : ZMod 3) := by
    simpa using congrArg Multiplicative.toAdd hv
  have hij' := congrArg ZMod.val hij
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij'
  exact Fin.ext hij'

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem bruhat_support_same_cell_root
    (π : (LocalField F q)ˣ)
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (j : Fin 3) (x : LocalField F q)
    (hg : eta F ζ hζ q π j * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈
        bruhatSupport F ζ hζ q S P π j m) :
    x ∈ rootLevelSet F ζ hζ q m := by
  obtain ⟨b, k, hk, he⟩ := hg
  obtain ⟨g, rfl⟩ := hk
  have hb : (b : ActualCover F ζ hζ q) ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q := by
    change (b : ActualCover F ζ hζ q) ∈ actualBorel F ζ hζ q
    rw [← S.borel_eq]
    exact (inBorel F ζ hζ q S P b).property
  obtain ⟨B, hB, hB10⟩ := hb
  have hp := congrArg (KPLocalSmoothRepresentation.projection F ζ hζ q) he
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (LocalField F q) (π ^ j.val) 1 *
        KPStandardLocalRootLifts.weylSwap (LocalField F q) *
        KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
      (B * KubotaRankTwo.d (LocalField F q) (π ^ j.val) 1 * g.val *
        KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simp only [map_mul, ← hB] at hp
    exact hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp'
  have h10 := congrArg (fun A : GL (Fin 2) (LocalField F q) => A 1 0) hc
  have h11 := congrArg (fun A : GL (Fin 2) (LocalField F q) => A 1 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.d,
    KubotaRankTwo.n, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
    hB10] at h10 h11
  have hB11 : B 1 1 ≠ 0 := by
    intro h
    have hc0 : (c : LocalField F q) = 0 := by simpa [h] using h10
    exact c.ne_zero hc0
  have hx : x * g.val 1 1 = g.val 1 0 := by
    apply mul_left_cancel₀ hB11
    calc
      _ = x * (B 1 1 * g.val 1 1) := by ring
      _ = x * (c : LocalField F q) := by rw [h10]
      _ = _ := h11
  obtain ⟨g₀, hg₀, he₀⟩ := g.property
  have hentries := (KPLocalCube.mem_integerCongruence_iff F q m g₀).mp hg₀
  have h11ideal : g₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 1
  have h10ideal : g₀ 1 0 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 0
  have hu : IsUnit (g₀ 1 1) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    have hmem : g₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q :=
      Ideal.pow_le_self (by have := hm.1; omega) h11ideal
    change 1 - g₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
    simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
  obtain ⟨u, hu⟩ := hu
  let y : KPLocalCube.LocalIntegers F q := g₀ 1 0 * (↑u⁻¹)
  have hyideal : y ∈ KPLocalCube.maximalIdeal F q ^ m :=
    (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _ h10ideal
  have hy : (y : LocalField F q) = x := by
    have hx' : x * (g₀ 1 1 : LocalField F q) = (g₀ 1 0 : LocalField F q) := by
      simpa only [← he₀, KPLocalCube.integerInclusion,
        Matrix.GeneralLinearGroup.map_apply, Subring.subtype_apply] using hx
    have huf : (u : LocalField F q) ≠ 0 := by
      exact (Units.map (KPLocalCube.LocalIntegers F q).subtype.toMonoidHom u).ne_zero
    apply (mul_right_cancel₀ huf)
    rw [← hu] at hx'
    have hyu : (y : LocalField F q) * (u : LocalField F q) =
        (g₀ 1 0 : LocalField F q) := by
      change ((g₀ 1 0 * (↑u⁻¹) * ↑u : KPLocalCube.LocalIntegers F q) : LocalField F q) = _
      simp only [mul_assoc, Units.inv_mul, mul_one]
    exact hyu.trans hx'.symm
  let n₀ : KPLocalCube.IntegerGL2 F q :=
    ⟨!![1,y;0,1], !![1,-y;0,1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]⟩
  have hn₀ : n₀ ∈ KPLocalCube.integerCongruence F q m := by
    rw [KPLocalCube.mem_integerCongruence_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [n₀, hyideal]
  have hn : KubotaRankTwo.n (LocalField F q) x ∈ KPLocalCube.Gamma F q m := by
    refine ⟨n₀, hn₀, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [n₀, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply,
        KubotaRankTwo.n, hy]
  exact ⟨⟨KubotaRankTwo.n (LocalField F q) x, hn⟩, rfl⟩

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

 def integralSwap : KPLocalCube.IntegerGL2 F q :=
  ⟨!![0,1;1,0], !![0,1;1,0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]⟩
private lemma integralSwap_map : KPLocalCube.integerInclusion F q (integralSwap F q) =
    KPStandardLocalRootLifts.weylSwap (LocalField F q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [integralSwap, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, KPStandardLocalRootLifts.weylSwap]
private lemma gamma_swap (m : ℕ) (k : KPLocalCube.LocalGL2 F q)
    (hk : k ∈ KPLocalCube.Gamma F q m) :
    KPStandardLocalRootLifts.weylSwap (LocalField F q) * k *
      (KPStandardLocalRootLifts.weylSwap (LocalField F q))⁻¹ ∈ KPLocalCube.Gamma F q m := by
  obtain ⟨g, hg, he⟩ := hk
  refine ⟨integralSwap F q * g * (integralSwap F q)⁻¹, ?_, ?_⟩
  · have hn : (KPLocalCube.integerCongruence F q m).Normal := by
      unfold KPLocalCube.integerCongruence
      infer_instance
    exact hn.conj_mem g hg _
  · simp only [map_mul, map_inv, integralSwap_map, he]
private lemma gamma_antitone {m r : ℕ} (hm : r ≤ m) :
    KPLocalCube.Gamma F q m ≤ KPLocalCube.Gamma F q r := by
  apply Subgroup.map_mono
  intro g hg
  rw [KPLocalCube.mem_integerCongruence_iff] at hg ⊢
  intro i j
  exact Ideal.pow_le_pow_right hm (hg i j)
private lemma eventually_normalized :
    ∃ r : ℕ, ∀ m ≥ r, ∀ k : ActualCover F ζ hζ q,
      k ∈ splitCongruenceSet F ζ hζ q m ↔
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ splitCongruenceSet F ζ hζ q m := by
  obtain ⟨d, hd, hcubes, hbasis, hcharts⟩ := KPLocalCube.deep_principal_units_and_matrix_charts F q
  obtain ⟨r, hr, hconj⟩ := KPDeepConjugationGerms.raw_extension_conjugation_near_identity
    F ζ hζ q d hd (hcharts d le_rfl).2.2 (KPStandardLocalRootLifts.weylSwap (LocalField F q))
  refine ⟨r, ?_⟩
  intro m hm
  have hf : ∀ k : ActualCover F ζ hζ q,
      k ∈ splitCongruenceSet F ζ hζ q m →
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ splitCongruenceSet F ζ hζ q m := by
    intro k hk
    obtain ⟨g, rfl⟩ := hk
    let g' := KPStandardLocalRootLifts.weylSwap (LocalField F q) * g.val *
      (KPStandardLocalRootLifts.weylSwap (LocalField F q))⁻¹
    have hg' : g' ∈ KPLocalCube.Gamma F q m := gamma_swap F q m g.val g.property
    have he := (hconj g.val (gamma_antitone F q hm g.property)).2
      (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q)) rfl
    refine ⟨⟨g', hg'⟩, ?_⟩
    exact (congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) he).symm.trans (by
      simp only [map_mul, map_inv]; rfl)
  intro k
  constructor
  · exact hf k
  · intro hk
    have hw : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ = KPPGLLocalCover.W F ζ hζ (Sum.inr q) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q))
    have hh := hf _ hk
    have he : KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k * (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹) *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ = k := by
      rw [hw]
      have hs : KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) = 1 := by
        simpa only [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q)
      calc
        _ = (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) * k *
          (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) := by group
        _ = k := by rw [hs]; simp
    rwa [he] at hh

private theorem polarization_kernel_open {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) :
    IsOpen {h : P.L.comap T.π | P.ωL h = 1} := by
  let J : Subgroup H := T.ω.toMonoidHom.ker.map T.C.subtype
  have hJ : IsOpen (J : Set H) :=
    T.center_open.isOpenMap_subtype_val _ T.character_kernel_open
  have hJP : J ≤ P.L.comap T.π := by
    intro h hh
    obtain ⟨c, hc, rfl⟩ := hh
    have hc' : (c : H) ∈ T.π.ker := by rw [T.quotient_kernel]; exact c.property
    change T.π (c : H) ∈ P.L
    rw [show T.π (c : H) = 1 from hc']
    exact P.L.one_mem
  let JP : Subgroup (P.L.comap T.π) := J.comap (P.L.comap T.π).subtype
  have hop : IsOpen (JP : Set (P.L.comap T.π)) := hJ.preimage continuous_subtype_val
  have hle : JP ≤ P.ωL.toMonoidHom.ker := by
    intro h hh
    obtain ⟨c, hc, he⟩ := hh
    change (c : H) = (h : H) at he
    have hc' : (h : H) ∈ T.C := he ▸ c.property
    change P.ωL h = 1
    rw [P.extends_center h hc']
    have hh : (⟨(h : H), hc'⟩ : T.C) = c := Subtype.ext he.symm
    rw [hh]
    exact hc
  exact Subgroup.isOpen_mono hle hop

private theorem unit_sphere_open : IsOpen {y : (LocalField F q)ˣ | valuation (LocalField F q) (y : LocalField F q) = 1} := by
  have h := Valuation.isOpen_sphere (v := valuation (LocalField F q)) (by simp : (1 : (valuation (LocalField F q)).ValueGroup₀) ≠ 0)
  have h' : IsOpen {x : LocalField F q | valuation (LocalField F q) x = 1} := by
    convert h using 1
    ext x
    simp only [Valuation.restrict_eq_one_iff]
  exact h'.preimage Units.continuous_val
private theorem chi_neighborhood
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) :
    ∃ U : Set (ActualCover F ζ hζ q), IsOpen U ∧ 1 ∈ U ∧
      ∀ b : BL F ζ hζ q S P, (b : ActualCover F ζ hζ q) ∈ U → chi F ζ hζ q S P hP ε b = 1 := by
  have hc : Continuous (retractL F ζ hζ q S P) := by
    apply Continuous.subtype_mk
    exact S.borel.retract_continuous.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hw : Continuous (weylHL F ζ hζ q S P hP) := by
    apply Continuous.subtype_mk
    exact S.borel.weyl.continuous.comp continuous_subtype_val
  let U : Set (HL F ζ hζ q S P) := {h | P.ωL h = 1 ∧
    P.ωL (weylHL F ζ hζ q S P hP h) = 1 ∧
    valuation (LocalField F q) (S.borel.coordinate h : LocalField F q) = 1}
  have hU : IsOpen U := (polarization_kernel_open S.heisenberg P).inter
    (((polarization_kernel_open S.heisenberg P).preimage hw).inter
      ((unit_sphere_open F q).preimage (S.borel.coordinate_continuous.comp continuous_subtype_val)))
  have hone : retractL F ζ hζ q S P 1 = 1 := by
    apply Subtype.ext
    change S.borel.retract (inBorel F ζ hζ q S P 1) = 1
    rw [show inBorel F ζ hζ q S P 1 = 1 from Subtype.ext rfl, map_one]
  have hV : IsOpen ((retractL F ζ hζ q S P) ⁻¹' U) := hU.preimage hc
  obtain ⟨V, hVo, heV⟩ := isOpen_induced_iff.mp hV
  refine ⟨V, hVo, ?_, ?_⟩
  · change (1 : BL F ζ hζ q S P) ∈ Subtype.val ⁻¹' V
    rw [heV]
    simp [U, hone]
  · intro b hb
    have hh : retractL F ζ hζ q S P b ∈ U := by
      change b ∈ (retractL F ζ hζ q S P) ⁻¹' U
      rw [← heV]
      exact hb
    obtain ⟨hp, hm, hv⟩ := hh
    have ha : localAbs (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) = 1 := by
      simp [localAbs, hv]
    cases ε <;> simp [chi, chiH, hp, hm, normPower, ha]
private theorem eventually_split_subset (U : Set (ActualCover F ζ hζ q))
    (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ r : ℕ, ∀ m ≥ r, splitCongruenceSet F ζ hζ q m ⊆ U := by
  obtain ⟨d, hd, hcubes, hbasis, hcharts⟩ := KPLocalCube.deep_principal_units_and_matrix_charts F q
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q d
  have htop : KPRankOneOpenCellKernel.coverTopology F ζ hζ q = KPPGLLocalCover.finiteTopology F ζ hζ q d :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ q _ d
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q) ⟨hd, (hcharts d le_rfl).2.2⟩
  have hUc : @IsOpen _ (KPPGLLocalCover.finiteTopology F ζ hζ q d) U := by rwa [← htop]
  letI : TopologicalSpace (ActualCover F ζ hζ q) := KPPGLLocalCover.finiteTopology F ζ hζ q d
  have hq : Continuous (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) := by
    exact continuous_quotient_mk'
  have hc := (KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q d
    ⟨hd, (hcharts d le_rfl).2.2⟩ 1).continuous
  have ho : IsOpen ((KPLocalChartTopology.translatedChart F ζ hζ q d 1) ⁻¹'
      ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) ⁻¹' U)) :=
    (hUc.preimage hq).preimage hc
  obtain ⟨V, hV, he⟩ := isOpen_induced_iff.mp ho
  have hV1 : (1 : KPLocalCube.LocalGL2 F q) ∈ V := by
    have hone : (1 : KPLocalCube.Gamma F q d) ∈
        (KPLocalChartTopology.translatedChart F ζ hζ q d 1) ⁻¹'
          ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) ⁻¹' U) := by
      simpa [KPLocalChartTopology.translatedChart, show KPLocalCover.sectionMap F ζ hζ (Sum.inr q) 1 = 1 from rfl] using h1
    rw [← he] at hone
    exact hone
  obtain ⟨r, hr, hrV⟩ := hbasis.mem_iff.mp (hV.mem_nhds hV1)
  refine ⟨r, ?_⟩
  intro m hm k hk
  obtain ⟨g, rfl⟩ := hk
  have hgd : g.val ∈ KPLocalCube.Gamma F q d := by
    apply Subgroup.map_mono (show KPLocalCube.integerCongruence F q m ≤ KPLocalCube.integerCongruence F q d from ?_) g.property
    intro g hg
    rw [KPLocalCube.mem_integerCongruence_iff] at hg ⊢
    exact fun i j => Ideal.pow_le_pow_right (hr.trans hm) (hg i j)
  have hgr : g.val ∈ KPLocalCube.Gamma F q r := by
    apply Subgroup.map_mono (show KPLocalCube.integerCongruence F q m ≤ KPLocalCube.integerCongruence F q r from ?_) g.property
    intro g hg
    rw [KPLocalCube.mem_integerCongruence_iff] at hg ⊢
    exact fun i j => Ideal.pow_le_pow_right hm (hg i j)
  have hv : (⟨g.val, hgd⟩ : KPLocalCube.Gamma F q d) ∈ Subtype.val ⁻¹' V := hrV hgr
  rw [he] at hv
  simpa [KPLocalChartTopology.translatedChart] using hv
private theorem eventually_chi_descent
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign) (π : (LocalField F q)ˣ) :
    ∃ r : ℕ, ∀ m ≥ r, ∀ (j : Fin 3) (b : BL F ζ hζ q S P),
      (eta F ζ hζ q π j)⁻¹ * (b : ActualCover F ζ hζ q) * eta F ζ hζ q π j ∈
        splitCongruenceSet F ζ hζ q m → chi F ζ hζ q S P hP ε b = 1 := by
  obtain ⟨U, hU, h1, hchi⟩ := chi_neighborhood F ζ hζ q S P hP ε
  have ht : ∀ j : Fin 3, ∃ r : ℕ, ∀ m ≥ r, ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      eta F ζ hζ q π j * k * (eta F ζ hζ q π j)⁻¹ ∈ U := by
    intro j
    letI : IsTopologicalGroup (ActualCover F ζ hζ q) :=
      (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1
    have hc : Continuous (fun k : ActualCover F ζ hζ q => eta F ζ hζ q π j * k * (eta F ζ hζ q π j)⁻¹) := by fun_prop
    obtain ⟨r, hr⟩ := eventually_split_subset F ζ hζ q _ (hU.preimage hc) (by simp; exact h1)
    exact ⟨r, hr⟩
  choose r hr using ht
  refine ⟨Finset.univ.sup r, ?_⟩
  intro m hm j b hb
  apply hchi b
  have hmr : r j ≤ m := (Finset.le_sup (f := r) (Finset.mem_univ j)).trans hm
  have hh := hr j m hmr _ hb
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh
private theorem compact_open_split (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    ∃ K : OpenSubgroup (ActualCover F ζ hζ q),
      (K : Set (ActualCover F ζ hζ q)) = splitCongruenceSet F ζ hζ q m ∧
      IsCompact (K : Set (ActualCover F ζ hζ q)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  have htop : ActualFiniteTorus.coverTopology F ζ hζ q =
      KPPGLLocalCover.finiteTopology F ζ hζ q m :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ q _ m
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q) hm
  rw [htop]
  letI : TopologicalSpace (ActualCover F ζ hζ q) := KPPGLLocalCover.finiteTopology F ζ hζ q m
  have hsigma := KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ q m hm.2
  obtain ⟨s, hs, _, _⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ q m (fun g hg h hh => hsigma g h hg hh)
  let f := (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp s
  have he : (f.range : Set (ActualCover F ζ hζ q)) = splitCongruenceSet F ζ hζ q m := by
    simp only [MonoidHom.coe_range, splitCongruenceSet]
    congr 1
    funext k
    exact congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) (hs k)
  have hc : Continuous s := by
    have hh := (KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q m hm 1).continuous
    convert hh using 1
    funext k
    simp only [KPLocalChartTopology.translatedChart, one_mul, hs]
  have hq : Continuous (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) :=
    continuous_quotient_mk'
  have hopen : IsOpen (f.range : Set (ActualCover F ζ hζ q)) := by
    have hrange : Set.range s = Set.range (KPLocalChartTopology.translatedChart F ζ hζ q m 1) := by
      congr 1
      funext k
      simp only [KPLocalChartTopology.translatedChart, one_mul, hs]
    have hsopen : IsOpen (Set.range s) := by
      rw [hrange]
      exact (KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q m hm 1).isOpen_range
    change IsOpen (Set.range f)
    rw [show Set.range f = (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) '' Set.range s from Set.range_comp (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) s]
    exact QuotientGroup.isOpenMap_coe _ hsopen
  letI : CompactSpace (KPLocalCube.Gamma F q m) :=
    isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F q m hm.1).1
  exact ⟨⟨f.range, hopen⟩, he, isCompact_range (hq.comp hc)⟩

private theorem root_open_zero (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    IsOpen (rootLevelSet F ζ hζ q m) ∧
      (0 : LocalField F q) ∈ rootLevelSet F ζ hζ q m := by
  obtain ⟨K, hK, _⟩ := compact_open_split F ζ hζ q m hm
  have hc : Continuous (KPPGLLocalCover.N F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
  refine ⟨?_, ?_⟩
  · change IsOpen (KPPGLLocalCover.N F ζ hζ (Sum.inr q) ⁻¹' splitCongruenceSet F ζ hζ q m)
    rw [← hK]
    exact K.isOpen.preimage hc
  · change KPPGLLocalCover.N F ζ hζ (Sum.inr q) 0 ∈ splitCongruenceSet F ζ hζ q m
    rw [← hK]
    have hn : KPPGLLocalCover.N F ζ hζ (Sum.inr q) 0 = 1 := by
      exact map_one (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
    rw [hn]
    exact K.one_mem

private theorem root_subset_integer (m : ℕ) :
    rootLevelSet F ζ hζ q m ⊆ (ValuativeRel.valuation (LocalField F q)).integer := by
  intro x hx
  obtain ⟨g, hg⟩ := hx
  obtain ⟨g₀, hg₀, he₀⟩ := g.property
  have hp := congrArg (KPLocalSmoothRepresentation.projection F ζ hζ q) hg
  have hp' : Matrix.ProjGenLinGroup.mk (KPLocalCube.integerInclusion F q g₀) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) x) := by
    change KPLocalSmoothRepresentation.ordinaryPGLMap F q
        (KPPGLLocalCover.baseQuotient F (Sum.inr q) g.val) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q
        (KPPGLLocalCover.baseQuotient F (Sum.inr q) (KubotaRankTwo.n (LocalField F q) x)) at hp
    rw [← he₀] at hp
    exact hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp'
  have h00 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 0 0) hc
  have h01 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 0 1) hc
  have hdet := congrArg Matrix.GeneralLinearGroup.det hc
  have hvdet : ValuativeRel.valuation (LocalField F q)
      ((Matrix.GeneralLinearGroup.det (KPLocalCube.integerInclusion F q g₀) : (LocalField F q)ˣ) : LocalField F q) = 1 := by
    rw [show Matrix.GeneralLinearGroup.det (KPLocalCube.integerInclusion F q g₀) =
      (Units.map (KPLocalCube.LocalIntegers F q).subtype) (Matrix.GeneralLinearGroup.det g₀) from
      Matrix.GeneralLinearGroup.map_det _ _]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (ValuativeRel.valuation (LocalField F q)))).mp
        (Matrix.GeneralLinearGroup.det g₀).isUnit
  have hv : ValuativeRel.valuation (LocalField F q) (c : LocalField F q) = 1 := by
    have hd : (c : LocalField F q) ^ 2 =
        ((Matrix.GeneralLinearGroup.det (KPLocalCube.integerInclusion F q g₀) : (LocalField F q)ˣ) : LocalField F q)⁻¹ := by
      have hn : Matrix.GeneralLinearGroup.det (KubotaRankTwo.n (LocalField F q) x) = 1 := by
        apply Units.ext
        simp [KubotaRankTwo.n, Matrix.det_fin_two]
      have hd' : Matrix.GeneralLinearGroup.det (KPLocalCube.integerInclusion F q g₀) * c ^ 2 = 1 := by
        simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar, hn] using hdet
      have hv' := congrArg (fun u : (LocalField F q)ˣ => (u : LocalField F q)) hd'
      exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hv')
    have hv' := congrArg (ValuativeRel.valuation (LocalField F q)) hd
    rw [map_pow, map_inv₀, hvdet, inv_one] at hv'
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide : (2 : ℕ) ≠ 0)).mp hv'
  have hx' : x = (g₀ 0 1 : LocalField F q) * (c : LocalField F q) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal_apply, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using h01.symm
  rw [hx']
  change ValuativeRel.valuation (LocalField F q) _ ≤ 1
  rw [map_mul, hv, mul_one]
  exact (g₀ 0 1).property

private theorem root_compact (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    IsCompact (rootLevelSet F ζ hζ q m) := by
  letI : T2Space (ActualCover F ζ hζ q) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
  obtain ⟨K, hK, hcompact⟩ := compact_open_split F ζ hζ q m hm
  have hc : Continuous (KPPGLLocalCover.N F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
  have hclosed : IsClosed (rootLevelSet F ζ hζ q m) := by
    change IsClosed (KPPGLLocalCover.N F ζ hζ (Sum.inr q) ⁻¹' splitCongruenceSet F ζ hζ q m)
    rw [← hK]
    exact hcompact.isClosed.preimage hc
  have hI : IsCompact ((ValuativeRel.valuation (LocalField F q)).integer : Set (LocalField F q)) := by
    have hr := isCompact_range (continuous_subtype_val :
      Continuous (fun x : ↥(ValuativeRel.valuation (LocalField F q)).integer => (x : LocalField F q)))
    convert hr using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  exact hI.of_isClosed_subset hclosed (root_subset_integer F ζ hζ q m)

theorem eventually_actual_raw_bruhat_geometry
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ K : OpenSubgroup (ActualCover F ζ hζ q),
      (K : Set (ActualCover F ζ hζ q)) = splitCongruenceSet F ζ hζ q m ∧
      IsCompact (K : Set (ActualCover F ζ hζ q)) ∧
      (∀ k : ActualCover F ζ hζ q,
        k ∈ K ↔ KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
          (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ K) ∧
      (∀ (j : Fin 3) (b : BL F ζ hζ q S P),
        (eta F ζ hζ q π j)⁻¹ * (b : ActualCover F ζ hζ q) *
          eta F ζ hζ q π j ∈ K → chi F ζ hζ q S P hP ε b = 1) ∧
      IsCompact (rootLevelSet F ζ hζ q m) ∧
      IsOpen (rootLevelSet F ζ hζ q m) ∧
      (0 : LocalField F q) ∈ rootLevelSet F ζ hζ q m ∧
      rootLevelSet F ζ hζ q m ⊆ (valuation (LocalField F q)).integer ∧
      (∀ (i j : Fin 3) (x : LocalField F q),
        eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x ∈
            bruhatSupport F ζ hζ q S P π j m ↔
          i = j ∧ x ∈ rootLevelSet F ζ hζ q m) := by
  obtain ⟨d, hd, hcubes, hbasis, hcharts⟩ :=
    KPLocalCube.deep_principal_units_and_matrix_charts F q
  obtain ⟨r, hnormal⟩ := eventually_normalized F ζ hζ q
  obtain ⟨c, hc⟩ := eventually_chi_descent F ζ hζ q S P hP ε π
  refine ⟨max (max d r) c, ?_⟩
  intro m hm
  have hmdr : max d r ≤ m := (le_max_left (max d r) c).trans hm
  have hdm : d ≤ m := (le_max_left d r).trans hmdr
  have hrm : r ≤ m := (le_max_right d r).trans hmdr
  have hcm : c ≤ m := (le_max_right (max d r) c).trans hm
  have hdepth : KPLocalChartTopology.MatrixChartDepth F q m :=
    ⟨hd.trans hdm, (hcharts m hdm).2.2⟩
  obtain ⟨K, hK, hcompact⟩ := compact_open_split F ζ hζ q m hdepth
  obtain ⟨hopen, hzero⟩ := root_open_zero F ζ hζ q m hdepth
  refine ⟨K, hK, hcompact, ?_, ?_, root_compact F ζ hζ q m hdepth,
    hopen, hzero, root_subset_integer F ζ hζ q m, ?_⟩
  · intro k
    change k ∈ (K : Set (ActualCover F ζ hζ q)) ↔
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) * k *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ (K : Set (ActualCover F ζ hζ q))
    rw [hK]
    exact hnormal m hrm k
  · intro j b hb
    apply hc m hcm j b
    change _ ∈ (K : Set (ActualCover F ζ hζ q)) at hb
    rwa [hK] at hb
  · intro i j x
    constructor
    · intro hg
      have hij := bruhat_support_index_eq F ζ hζ q S P hP π hπ m hdepth i j x hg
      refine ⟨hij, ?_⟩
      subst j
      exact bruhat_support_same_cell_root F ζ hζ q S P π m hdepth i x hg
    · rintro ⟨rfl, hx⟩
      let w := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
      let n := KPPGLLocalCover.N F ζ hζ (Sum.inr q) x
      have hnx : n ∈ splitCongruenceSet F ζ hζ q m := hx
      have hwk : w * n * w⁻¹ ∈ splitCongruenceSet F ζ hζ q m :=
        (hnormal m hrm n).mp hnx
      refine ⟨1, w * n * w⁻¹, hwk, ?_⟩
      simp only [Subgroup.coe_one, one_mul]
      change eta F ζ hζ q π i * w * n = eta F ζ hζ q π i * (w * n * w⁻¹) * w
      group

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.BruhatGeometry

end

end
