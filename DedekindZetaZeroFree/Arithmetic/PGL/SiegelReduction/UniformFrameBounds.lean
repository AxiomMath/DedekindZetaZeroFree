module

public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CoverFromFrameBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.RationalLineOrbitClassification

@[expose] public section

section

noncomputable section
open scoped Classical Matrix

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

 abbrev coordinates : (Fin 2 → F) ≃ₗ[F] F × F :=
  LinearEquiv.finTwoArrow F F

 def coordinateLattice
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M) :
    FullLattice (KPCuspArithmetic.Order F) F :=
  ⟨M.map ((coordinates F).restrictScalars (KPCuspArithmetic.Order F)).toLinearMap,
    { fg := by
        letI := hM.1
        exact (Submodule.FG.of_finite (N := M)).map _
      span_eq_top := by
        rw [Submodule.map_coe]
        change Submodule.span F ((coordinates F).toLinearMap '' (M : Set _)) = ⊤
        rw [← Submodule.map_span, hM.2]
        apply top_unique
        intro v _
        exact Submodule.mem_map.mpr ⟨(coordinates F).symm v, trivial,
          (coordinates F).apply_symm_apply v⟩ }⟩

private theorem coordinate_orbit
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (q r : RationalLine F)
    (h : lineEquivalent (KPCuspArithmetic.Order F) F (coordinateLattice F M hM).val q r) :
    MulAction.orbitRel (KPCuspArithmetic.projectiveAutomorphisms F M)
      (KPCuspArithmetic.Cusp F)
      (Projectivization.map (coordinates F).symm.toLinearMap (coordinates F).symm.injective q)
      (Projectivization.map (coordinates F).symm.toLinearMap (coordinates F).symm.injective r) := by
  obtain ⟨g, hg, hq⟩ := h
  let f := ((coordinates F).trans g).trans (coordinates F).symm
  let A := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv f)
  have hAv (v : Fin 2 → F) : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = f v := by
    have hh := congrArg (fun u : LinearMap.GeneralLinearGroup F (Fin 2 → F) => u.val v)
      (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
        (LinearMap.GeneralLinearGroup.ofLinearEquiv f))
    exact hh
  have hf : Submodule.map (f.restrictScalars (KPCuspArithmetic.Order F)).toLinearMap M = M := by
    change Submodule.map (((coordinates F).symm.restrictScalars _).toLinearMap.comp
      ((g.restrictScalars _).toLinearMap.comp ((coordinates F).restrictScalars _).toLinearMap)) M = M
    rw [Submodule.map_comp, Submodule.map_comp]
    change Submodule.map ((coordinates F).symm.restrictScalars _).toLinearMap
      (Submodule.map (g.restrictScalars _).toLinearMap (coordinateLattice F M hM).val) = M
    change Submodule.map (g.restrictScalars (KPCuspArithmetic.Order F)).toLinearMap
      (M.map ((coordinates F).restrictScalars _).toLinearMap) =
      M.map ((coordinates F).restrictScalars _).toLinearMap at hg
    change Submodule.map ((coordinates F).symm.restrictScalars _).toLinearMap
      (Submodule.map (g.restrictScalars _).toLinearMap
        (M.map ((coordinates F).restrictScalars _).toLinearMap)) = M
    rw [hg]
    ext v
    simp only [Submodule.mem_map_equiv]
    change (coordinates F).symm ((coordinates F) v) ∈ M ↔ v ∈ M
    rw [LinearEquiv.symm_apply_apply]
  have hA : Matrix.ProjGenLinGroup.mk A ∈ KPCuspArithmetic.projectiveAutomorphisms F M := by
    apply (KPCuspArithmetic.mem_projectiveAutomorphisms_iff F M _).mpr
    refine ⟨A, rfl, fun v => ?_⟩
    rw [hAv]
    have hh : f v ∈ Submodule.map (f.restrictScalars _).toLinearMap M ↔ v ∈ M := by
      rw [Submodule.mem_map_equiv]
      change f.symm (f v) ∈ M ↔ v ∈ M
      rw [LinearEquiv.symm_apply_apply]
    rw [hf] at hh
    exact hh.symm
  apply (MulAction.orbitRel (KPCuspArithmetic.projectiveAutomorphisms F M)
    (KPCuspArithmetic.Cusp F)).symm
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨⟨Matrix.ProjGenLinGroup.mk A, hA⟩, ?_⟩
  rw [← hq]
  induction q using Projectivization.ind with
  | h v hv =>
    simp only [Projectivization.map_mk]
    change Matrix.ProjGenLinGroup.mk A •
      Projectivization.mk F ((coordinates F).symm v) _ =
      Projectivization.mk F ((coordinates F).symm (g v)) _
    rw [Projectivization.PGL.mk_smul_mk]
    congr 1
    change (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (coordinates F).symm v = _
    rw [hAv]
    simp [f]

theorem finite_integral_cusp_orbits
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M) :
    Finite (Quotient (MulAction.orbitRel (KPCuspArithmetic.projectiveAutomorphisms F M)
      (KPCuspArithmetic.Cusp F))) := by
  let L := coordinateLattice F M hM
  letI := kp_cusp_numberField_finite_lineOrbits F L
  let p : Quotient (lineSetoid (KPCuspArithmetic.Order F) F L.val) →
      Quotient (MulAction.orbitRel (KPCuspArithmetic.projectiveAutomorphisms F M)
        (KPCuspArithmetic.Cusp F)) :=
    Quotient.map (Projectivization.map (coordinates F).symm.toLinearMap
      (coordinates F).symm.injective) (coordinate_orbit F M hM)
  apply Finite.of_surjective p
  intro z
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective z
  refine ⟨Quotient.mk _ (Projectivization.map (coordinates F).toLinearMap
    (coordinates F).injective q), ?_⟩
  induction q using Projectivization.ind with
  | h v hv =>
    change Quotient.mk _ (Projectivization.map (coordinates F).symm.toLinearMap
      (coordinates F).symm.injective (Projectivization.map (coordinates F).toLinearMap
        (coordinates F).injective (Projectivization.mk F v hv))) = _
    rw [Projectivization.map_mk, Projectivization.map_mk]
    congr 2
    exact (coordinates F).symm_apply_apply v

theorem finite_arithmetic_cusp_orbits
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M)) :
    Finite (Quotient (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F))) := by
  let G := KPCuspArithmetic.projectiveAutomorphisms F M
  have hle : Γ ≤ G := fun g hg =>
    (KPCuspArithmetic.preservesUpToHomothety_iff_mem_projectiveAutomorphisms F M g).mp (hΓ g hg)
  let H := Γ.subgroupOf G
  letI : H.FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hcomm.1
  letI := finite_integral_cusp_orbits F M hM
  letI : Finite (Quotient (MulAction.orbitRel H (KPCuspArithmetic.Cusp F))) := inferInstance
  let p : Quotient (MulAction.orbitRel H (KPCuspArithmetic.Cusp F)) →
      Quotient (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)) :=
    Quotient.map id (by
      intro x y h
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨⟨g.val.val, g.property⟩, hg⟩)
  apply Finite.of_surjective p
  intro z
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective z
  exact ⟨Quotient.mk _ q, rfl⟩

theorem exists_cusp_frame (q : KPCuspArithmetic.Cusp F) :
    ∃ σ : KPCuspArithmetic.PGL2 F, σ • KPCuspArithmetic.infinity F = q := by
  let v := q.rep
  have hv : v ≠ 0 := q.rep_nonzero
  have hcol (A : Matrix.GeneralLinearGroup (Fin 2) F)
      (hc : A 0 0 = v 0 ∧ A 1 0 = v 1) :
      Matrix.ProjGenLinGroup.mk A • KPCuspArithmetic.infinity F = q := by
    rw [KPCuspArithmetic.infinity, Projectivization.PGL.mk_smul_mk,
      ← Projectivization.mk_rep q]
    congr 1
    change (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = v
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    let A := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![v 0, 1; v 1, 0] (by simpa [Matrix.det_fin_two] using h1)
    exact ⟨Matrix.ProjGenLinGroup.mk A, hcol A ⟨rfl, rfl⟩⟩
  · let A := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![v 0, 0; v 1, 1] (by simpa [Matrix.det_fin_two] using h0)
    exact ⟨Matrix.ProjGenLinGroup.mk A, hcol A ⟨rfl, rfl⟩⟩

theorem exists_finite_cusp_frames
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M)) :
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) := by
  let Q := Quotient (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F))
  letI : Finite Q := finite_arithmetic_cusp_orbits F M hM Γ hΓ hcomm
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Nonempty Q := ⟨Quotient.mk _ (KPCuspArithmetic.infinity F)⟩
  let e := Fintype.equivFin Q
  let q : Fin (Fintype.card Q) → KPCuspArithmetic.Cusp F := fun a => (e.symm a).out
  choose σ hσ using fun a => exists_cusp_frame F (q a)
  refine ⟨Fintype.card Q, q, σ, Fintype.card_pos, hσ, ?_, ?_⟩
  · intro r
    let a := e (Quotient.mk _ r)
    have he : Quotient.mk (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)) (q a) =
        Quotient.mk _ r := by
      change Quotient.mk _ (e.symm (e (Quotient.mk _ r))).out = Quotient.mk _ r
      rw [Equiv.symm_apply_apply, Quotient.out_eq]
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact he.symm))
    exact ⟨a, γ, hγ⟩
  · intro a b hab γ hγ
    apply hab
    have he : Quotient.mk (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)) (q a) =
        Quotient.mk _ (q b) := by
      apply Quotient.sound
      apply (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)).symm
      exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, hγ⟩)
    have hout (a) : Quotient.mk (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)) (q a) =
        e.symm a := Quotient.out_eq _
    rw [hout, hout] at he
    exact e.symm.injective he

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors
namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem integral_lattice_determinant_unit
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ v, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) :
    ∃ u : (NumberField.RingOfIntegers F)ˣ,
      algebraMap (NumberField.RingOfIntegers F) F (u : NumberField.RingOfIntegers F) =
        (A : Matrix (Fin 2) (Fin 2) F).det := by
  let e := LinearEquiv.finTwoArrow F F
  let L : FullLattice (NumberField.RingOfIntegers F) F :=
    ⟨M.map (e.restrictScalars _).toLinearMap,
      { fg := by
          letI := hM.1
          exact (Submodule.FG.of_finite (N := M)).map _
        span_eq_top := by
          rw [Submodule.map_coe]
          change Submodule.span F (e.toLinearMap '' (M : Set _)) = ⊤
          rw [← Submodule.map_span, hM.2]
          apply top_unique
          intro v _
          exact Submodule.mem_map.mpr ⟨e.symm v, trivial, e.apply_symm_apply v⟩ }⟩
  let f := (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv
  let g := (e.symm.trans f).trans e
  have hmap : Submodule.map (g.restrictScalars _).toLinearMap L.val = L.val := by
    ext x
    simp only [Submodule.mem_map_equiv]
    change g.symm x ∈ Submodule.map (e.restrictScalars _).toLinearMap M ↔
      x ∈ Submodule.map (e.restrictScalars _).toLinearMap M
    simp only [Submodule.mem_map_equiv]
    change e.symm (g.symm x) ∈ M ↔ e.symm x ∈ M
    simp only [g, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have hh := hA (f.symm (e.symm x))
    change f.symm (e.symm x) ∈ M ↔ f (f.symm (e.symm x)) ∈ M at hh
    simpa using hh
  have hd : LinearMap.det g.toLinearMap = (A : Matrix (Fin 2) (Fin 2) F).det := by
    change LinearMap.det (e.toLinearMap ∘ₗ f.toLinearMap ∘ₗ e.symm.toLinearMap) = _
    rw [LinearMap.det_conj]
    change LinearMap.det (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) F)) = _
    simp
  let N := determinantSubmodule (NumberField.RingOfIntegers F) F L.val
  have hs : Submodule.map (LinearMap.mulLeft (NumberField.RingOfIntegers F)
      (A : Matrix (Fin 2) (Fin 2) F).det) N = N := by
    rw [← hd, ← kp_cusp_determinantSubmodule_map]
    change determinantSubmodule (NumberField.RingOfIntegers F) F
      (Submodule.map (g.restrictScalars _).toLinearMap L.val) = N
    rw [hmap]
  have hg : ∀ x ∈ N, (A : Matrix (Fin 2) (Fin 2) F).det * x ∈ N := by
    intro x hx
    rw [← hs]
    exact Submodule.mem_map_of_mem hx
  have hi : ∀ x ∈ N, ((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ).val * x ∈ N := by
    intro x hx
    rw [← hs] at hx
    obtain ⟨y, hy, he⟩ := hx
    change (A : Matrix (Fin 2) (Fin 2) F).det * y = x at he
    rw [← he, ← mul_assoc]
    change ((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ).val *
      (Matrix.GeneralLinearGroup.det A : Fˣ).val * y ∈ N
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    exact hy
  have hu := KPCuspParabolicLattices.scalar_integral_unit F
    (Matrix.GeneralLinearGroup.det A) N N
    (kp_cusp_determinantSubmodule_ne_bot _ _ L)
    (kp_cusp_determinantSubmodule_ne_bot _ _ L)
    (kp_cusp_determinantSubmodule_fg _ _ L)
    (kp_cusp_determinantSubmodule_fg _ _ L) hg hi
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, congrArg Units.val hu⟩

theorem fractional_absNorm_antitone
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJ : J ≠ 0) (h : I ≤ J) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hmul : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul_of_nonneg_right h zero_le
         _ = 1 := by rw [mul_inv_cancel₀ hJ]
  obtain ⟨K, hK⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hmul
  have hK0 : K ≠ ⊥ := by
    intro hzero
    have hz : I * J⁻¹ = 0 := by rw [← hK, hzero, FractionalIdeal.coeIdeal_bot]
    exact (mul_ne_zero hI (inv_ne_zero hJ)) hz
  have hnorm : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hK, FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hK0)
  have hp : 0 < FractionalIdeal.absNorm J :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J)
      (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hJ))
  rw [map_mul, map_inv₀, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul] at hnorm
  exact hnorm

theorem integral_lattice_entry_denominator
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M) :
    ∃ c : F, c ≠ 0 ∧ ∀ A : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ v, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) →
      ∀ i j, c * A i j ∈ (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) := by
  letI : Submodule.IsLattice F M := ⟨Module.Finite.iff_fg.mp hM.1, hM.2⟩
  have hd (i : Fin 2) : ∃ c : (NumberField.RingOfIntegers F)⁰,
      ∀ v ∈ M, algebraMap (NumberField.RingOfIntegers F) F c * v i ∈
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) := by
    let p : (Fin 2 → F) →ₗ[NumberField.RingOfIntegers F] F := LinearMap.proj i
    obtain ⟨c, hc⟩ := FractionalIdeal.isFractional_of_fg
      (S := (NumberField.RingOfIntegers F)⁰) ((Module.Finite.iff_fg.mp hM.1).map p)
    refine ⟨⟨c, hc.1⟩, fun v hv => ?_⟩
    have hh := hc.2 (p v) (Submodule.mem_map_of_mem hv)
    exact (FractionalIdeal.mem_one_iff _).mpr hh
  choose c hc using hd
  have hr (j : Fin 2) : ∃ r : NumberField.RingOfIntegers F, r ≠ 0 ∧
      algebraMap (NumberField.RingOfIntegers F) F r • Pi.single j (1 : F) ∈ M :=
    kp_cusp_full_lattice_clear_denominators _ F _ M (Pi.single j 1)
  choose r hr hrv using hr
  let d : NumberField.RingOfIntegers F := c 0 * c 1 * (r 0 * r 1)
  have hd0 : d ≠ 0 := mul_ne_zero
    (mul_ne_zero (nonZeroDivisors.ne_zero (c 0).property)
      (nonZeroDivisors.ne_zero (c 1).property)) (mul_ne_zero (hr 0) (hr 1))
  refine ⟨algebraMap (NumberField.RingOfIntegers F) F d,
    (map_ne_zero_iff _ (IsFractionRing.injective _ F)).mpr hd0, ?_⟩
  intro A hA i j
  have hh := hc i ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ
    (algebraMap (NumberField.RingOfIntegers F) F (r j) • Pi.single j 1))
    ((hA _).mp (hrv j))
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at hh
  change algebraMap (NumberField.RingOfIntegers F) F (c i) *
    (algebraMap (NumberField.RingOfIntegers F) F (r j) * A i j) ∈ _ at hh
  have hscale (a : NumberField.RingOfIntegers F) :
      algebraMap (NumberField.RingOfIntegers F) F a *
        (algebraMap (NumberField.RingOfIntegers F) F (c i) *
          (algebraMap (NumberField.RingOfIntegers F) F (r j) * A i j)) ∈
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) := by
    simpa only [one_mul] using FractionalIdeal.mul_mem_mul
      (FractionalIdeal.coe_mem_one (S := (NumberField.RingOfIntegers F)⁰) a) hh
  fin_cases i <;> fin_cases j
  · convert hscale ((c 1 : NumberField.RingOfIntegers F) * r 1) using 1 <;> simp [d, map_mul] <;> ring
  · convert hscale ((c 1 : NumberField.RingOfIntegers F) * r 0) using 1 <;> simp [d, map_mul] <;> ring
  · convert hscale ((c 0 : NumberField.RingOfIntegers F) * r 1) using 1 <;> simp [d, map_mul] <;> ring
  · convert hscale ((c 0 : NumberField.RingOfIntegers F) * r 0) using 1 <;> simp [d, map_mul] <;> ring

theorem lower_row_content_mul_le
    (A G : Matrix.GeneralLinearGroup (Fin 2) F) (c : F)
    (hc : ∀ i j, c * G i j ∈
      (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) :
    FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ c *
      KPCusp.content F 1 (frameLowerRow F (A * G)) ≤
        KPCusp.content F 1 (frameLowerRow F A) := by
  have hentry (k j : Fin 2) : A 1 k * (c * G k j) ∈
      KPCusp.content F 1 (frameLowerRow F A) := by
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).mp (hc k j)
    rw [← hu, mul_comm]
    change u • A 1 k ∈ _
    apply Submodule.smul_mem
    fin_cases k
    · apply (show FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (A 1 0) ≤
          KPCusp.content F 1 (frameLowerRow F A) from le_add_of_nonneg_right zero_le)
      exact FractionalIdeal.mem_spanSingleton_self _ _
    · apply (show FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (A 1 1) ≤
          KPCusp.content F 1 (frameLowerRow F A) from by
            simp only [KPCusp.content, frameLowerRow, mul_one]
            exact le_add_of_nonneg_left zero_le)
      exact FractionalIdeal.mem_spanSingleton_self _ _
  have hcol (j : Fin 2) : c * (A * G) 1 j ∈
      KPCusp.content F 1 (frameLowerRow F A) := by
    have hh := Submodule.add_mem (KPCusp.content F 1 (frameLowerRow F A)).val
      (hentry 0 j) (hentry 1 j)
    change A 1 0 * (c * G 0 j) + A 1 1 * (c * G 1 j) ∈
      KPCusp.content F 1 (frameLowerRow F A) at hh
    convert hh using 1
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  change FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ c *
    (FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ ((A * G) 1 0) +
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ ((A * G) 1 1) * 1) ≤ _
  rw [mul_one, mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.sup_eq_add]
  exact sup_le
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr (hcol 0))
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr (hcol 1))

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors
namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem frameHeightConstant_eq_of_mk_eq
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    frameHeightConstant F 1 A = frameHeightConstant F 1 B := by
  have hr : rowCusp F (frameLowerRow F A) = rowCusp F (frameLowerRow F B) := by
    rw [rowCusp_frameLowerRow, rowCusp_frameLowerRow, map_inv, map_inv, h]
  have hh := KPCusp.normalizedHeight_eq_of_flag_eq F hF 1
    (frameLowerRow F A) (frameLowerRow F B)
    (flag_eq_of_rowCusp_eq F _ _ hr) (fun _ => (0, 0))
  rw [normalizedHeight_frame_lower_row, normalizedHeight_frame_lower_row] at hh
  change frameHeightConstant F 1 A * _ = frameHeightConstant F 1 B * _ at hh
  have ha : glAction F A (fun _ => (0, 0)) = glAction F B (fun _ => (0, 0)) := by
    rw [← action_mk, ← action_mk, h]
  rw [ha] at hh
  exact mul_right_cancel₀ (ne_of_gt (Real.exp_pos _)) hh

theorem complex_det_norm_product_sq
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) ^ 2 =
        (|Algebra.norm ℚ (A : Matrix (Fin 2) (Fin 2) F).det| : ℝ) := by
  letI : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp hF
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
  simp only [NumberField.IsTotallyComplex.mult_eq]
  let e : Fin (NumberField.InfinitePlace.nrComplexPlaces F) ≃ NumberField.InfinitePlace F :=
    (Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}).symm.trans
      (Equiv.subtypeUnivEquiv fun w => NumberField.IsTotallyComplex.isComplex w)
  apply Fintype.prod_equiv e
  intro i
  change ‖((KPCusp.complexPlace F i).embedding.mapMatrix (A : Matrix (Fin 2) (Fin 2) F)).det‖ ^ 2 = _
  rw [← RingHom.map_det]
  simp [e, KPCusp.complexPlace, NumberField.InfinitePlace.norm_embedding_eq]

theorem integral_lattice_complex_det_norm_product
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ v, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) :
    (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) = 1 := by
  obtain ⟨u, hu⟩ := integral_lattice_determinant_unit F M hM A hA
  have hs : FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰
      (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← hu]
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top]
  have hn : |Algebra.norm ℚ (A : Matrix (Fin 2) (Fin 2) F).det| = 1 := by
    rw [← FractionalIdeal.absNorm_span_singleton (R := NumberField.RingOfIntegers F), hs, map_one]
  have hp := complex_det_norm_product_sq F hF A
  rw [← Rat.cast_abs, hn, Rat.cast_one] at hp
  have hnonneg : 0 ≤ (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem integral_lattice_det_norm_mul
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (A G : Matrix.GeneralLinearGroup (Fin 2) F)
    (hG : ∀ v, v ∈ M ↔ (G : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) :
    (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding (A * G) :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) =
    (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) := by
  simp only [map_mul, Units.val_mul, Matrix.det_mul, norm_mul, Finset.prod_mul_distrib]
  rw [integral_lattice_complex_det_norm_product F hF M hM G hG, mul_one]

theorem integral_lattice_content_norm_bounds
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M) :
    ∃ k : ℝ, 0 < k ∧ ∀ A G : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ v, v ∈ M ↔ (G : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) →
      (FractionalIdeal.absNorm (KPCusp.content F 1 (frameLowerRow F A)) : ℝ) / k ≤
        (FractionalIdeal.absNorm (KPCusp.content F 1 (frameLowerRow F (A * G))) : ℝ) ∧
      (FractionalIdeal.absNorm (KPCusp.content F 1 (frameLowerRow F (A * G))) : ℝ) ≤
        k * (FractionalIdeal.absNorm (KPCusp.content F 1 (frameLowerRow F A)) : ℝ) := by
  obtain ⟨c, hc, hden⟩ := integral_lattice_entry_denominator F M hM
  let S := FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ c
  have hS : S ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc
  have hk : 0 < (FractionalIdeal.absNorm S : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg S)
      (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hS))
  have hn (A : Matrix.GeneralLinearGroup (Fin 2) F) :
      KPCusp.content F 1 (frameLowerRow F A) ≠ 0 := by
    have hp := frameHeightConstant_pos F 1 one_ne_zero A
    intro hz
    simp [frameHeightConstant, hz] at hp
  refine ⟨FractionalIdeal.absNorm S, hk, ?_⟩
  intro A G hG
  have hiG : ∀ v, v ∈ M ↔ (↑(G⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
    intro v
    have hh := hG ((↑(G⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at hh
    exact hh.symm
  have hl := fractional_absNorm_antitone F _ _ (mul_ne_zero hS (hn (A * G))) (hn A)
    (lower_row_content_mul_le F A G c (hden G hG))
  have hu := fractional_absNorm_antitone F _ _ (mul_ne_zero hS (hn A)) (hn (A * G))
    (by simpa only [mul_inv_cancel_right] using
      lower_row_content_mul_le F (A * G) G⁻¹ c (hden G⁻¹ hiG))
  rw [map_mul] at hl hu
  constructor
  · rw [div_le_iff₀ hk, mul_comm]
    exact_mod_cast hl
  · exact_mod_cast hu

theorem exists_projective_frame_bounds
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ G : Matrix.GeneralLinearGroup (Fin 2) F,
      Matrix.ProjGenLinGroup.mk G ∈ KPCuspArithmetic.projectiveAutomorphisms F M →
      c ≤ frameHeightConstant F 1 (A * G⁻¹) ∧ frameHeightConstant F 1 (A * G⁻¹) ≤ C := by
  obtain ⟨k, hk, hb⟩ := integral_lattice_content_norm_bounds F M hM
  have hA := frameHeightConstant_pos F 1 one_ne_zero A
  refine ⟨frameHeightConstant F 1 A / k, k * frameHeightConstant F 1 A,
    div_pos hA hk, mul_pos hk hA, ?_⟩
  intro G hG
  obtain ⟨H, hH, hh⟩ := (KPCuspArithmetic.mem_projectiveAutomorphisms_iff F M _).mp
    (Subgroup.inv_mem _ hG)
  have he : frameHeightConstant F 1 (A * G⁻¹) = frameHeightConstant F 1 (A * H) := by
    apply frameHeightConstant_eq_of_mk_eq F hF
    rw [map_mul, map_mul, hH]
    rfl
  rw [he]
  obtain ⟨hl, hu⟩ := hb A H hh
  have hd : 0 < (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖) := by
    exact Finset.prod_pos fun i _ => norm_pos_iff.mpr (Matrix.GeneralLinearGroup.map _ A).det_ne_zero
  unfold frameHeightConstant
  rw [integral_lattice_det_norm_mul F hF M hM A H hh]
  constructor
  · rw [div_div, mul_comm _ k, ← div_div]
    exact div_le_div_of_nonneg_right hl (le_of_lt hd)
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hu (le_of_lt hd)

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors
namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem exists_uniform_arithmetic_frame_bounds {n : ℕ} (hn : 0 < n)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (A : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk G ∈ Γ → c ≤ frameHeightConstant F 1 (A a * G⁻¹)) ∧
      (∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk G ∈ Γ → frameHeightConstant F 1 (A a * G⁻¹) ≤ C) := by
  choose c C hc hC hb using fun a => exists_projective_frame_bounds F hF M hM (A a)
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let c₀ := Finset.univ.inf' hu c
  let C₀ := Finset.univ.sup' hu C
  have hc₀ : 0 < c₀ := (Finset.lt_inf'_iff hu).mpr (fun a _ => hc a)
  have hC₀ : 0 < C₀ := (hC ⟨0, hn⟩).trans_le (Finset.le_sup' C (Finset.mem_univ _))
  have hle := KPCuspArithmetic.subgroup_le_projectiveAutomorphisms F M Γ hΓ
  refine ⟨c₀, C₀, hc₀, hC₀, ?_, ?_⟩
  · intro a G hG
    exact (Finset.inf'_le c (Finset.mem_univ a)).trans (hb a G (hle hG)).1
  · intro a G hG
    exact (hb a G (hle hG)).2.trans (Finset.le_sup' C (Finset.mem_univ a))

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors
namespace DedekindZetaZeroFree

theorem kp_cusp_siegel_cover_and_truncation_proved
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M)) :
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F) (t₀ : ℝ)
      (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) ∧
      (∀ a, IsCompact (P a) ∧ (P a).Nonempty ∧ IsCompact (B a) ∧ (B a).Nonempty) ∧
      (∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
          w ∈ KPCuspSiegel.box F (P a) (B a) (Set.Ici t₀) ∧
          z = KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F)
            (KPCuspSiegel.action F (σ a) w)) ∧
      (∀ (a : Fin n) (T : ℝ),
        KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T =
          KPCuspSiegel.projection F Γ ''
            (KPCuspSiegel.action F (σ a) ''
              KPCuspSiegel.box F (P a) (B a) (Set.Ioi T))) ∧
      (∀ T : ℝ, t₀ < T →
        IsCompact (KPCuspSiegel.projection F Γ ''
          (⋃ a : Fin n, KPCuspSiegel.action F (σ a) ''
            KPCuspSiegel.box F (P a) (B a) (Set.Icc t₀ T))) ∧
        IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
          (⋃ a : Fin n, KPCuspSiegel.projection F Γ ''
            KPCuspSiegel.highCusp F (σ a) T))) ∧
      ∃ T₁ : ℝ, t₀ < T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
        (Pairwise fun a b : Fin n =>
          Disjoint (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)
            (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ b) T)) ∧
        (∀ (a b : Fin n) (γ : Γ)
          (z : KPArch.Space (KPCuspLogShape.dimension F)),
          z ∈ KPCuspSiegel.highCusp F (σ a) T →
          KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F) z ∈
            KPCuspSiegel.highCusp F (σ b) T →
          a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ KPCuspSiegel.parabolic F Γ (q a)) ∧
        (∀ (a : Fin n) (g : KPCuspSiegel.parabolic F Γ (q a)),
          Set.MapsTo (KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F))
            (KPCuspSiegel.highCusp F (σ a) T) (KPCuspSiegel.highCusp F (σ a) T)) ∧
        (∀ a : Fin n,
          ∃ e : KPCuspSiegel.CuspQuotient F Γ (q a) (KPCuspSiegel.highCusp F (σ a) T) →
            KPCuspSiegel.OrbitQuotient F Γ,
            Topology.IsEmbedding e ∧
            (∀ z : KPCuspSiegel.highCusp F (σ a) T,
              e (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z)) := by
  obtain ⟨n, q, σ, hn, hσ, hcusps, hirr⟩ :=
    KPCuspSiegel.exists_finite_cusp_frames F M hM Γ hΓ hcomm
  choose A hA using fun a => Matrix.ProjGenLinGroup.mk_surjective (σ a)⁻¹
  have hframe (a : Fin n) :
      Matrix.ProjGenLinGroup.mk (A a)⁻¹ • KPCuspArithmetic.infinity F = q a := by
    rw [map_inv, hA, inv_inv]
    exact hσ a
  obtain ⟨c, C, hc, hC, hlo, hhi⟩ :=
    KPCuspSiegel.exists_uniform_arithmetic_frame_bounds F hn hF M hM Γ hΓ A
  obtain ⟨t₀, P, B, hPB, hcover, hhigh, hcompact, hends⟩ :=
    KPCuspSiegel.siegel_cover_of_uniform_frame_bounds F hF M hM Γ hΓ hcomm
      q A hframe hcusps hirr c C hc hC hlo hhi
  exact ⟨n, q, (fun a => Matrix.ProjGenLinGroup.mk (A a)⁻¹), t₀, P, B,
    hn, hframe, hcusps, hirr, hPB, hcover, hhigh, hcompact, hends⟩

end DedekindZetaZeroFree

end

end
