module

public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.SteinitzClassification

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

theorem kp_cusp_coefficientIdeal_smul
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0)
    (c : K) (hc : c ≠ 0) :
    coefficientIdeal R K M (c • v) (smul_ne_zero hc hv) =
      FractionalIdeal.spanSingleton R⁰ c⁻¹ * coefficientIdeal R K M v hv := by
  apply FractionalIdeal.ext
  intro t
  rw [FractionalIdeal.mem_singleton_mul]
  change t • (c • v) ∈ M.val ↔ ∃ s, s • v ∈ M.val ∧ t = c⁻¹ * s
  constructor
  · intro ht
    refine ⟨t * c, ?_, ?_⟩
    · simpa only [mul_smul] using ht
    · field_simp
  · rintro ⟨s, hs, rfl⟩
    rw [smul_smul]
    have he : c⁻¹ * s * c = s := by field_simp
    rw [he]
    exact hs

theorem kp_cusp_lineClass_mk
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) :
    lineClass R K M (Projectivization.mk K v hv) =
      ClassGroup.mk K (Units.mk0 (coefficientIdeal R K M v hv) (by
        intro h
        apply kp_cusp_coefficientSubmodule_ne_bot R K M v hv
        exact (congrArg Subtype.val h).trans FractionalIdeal.coe_zero)) := by
  unfold lineClass
  apply (kp_cusp_class_eq_iff_scalar R K _ _ _ _).mpr
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  refine ⟨(a : K), a.ne_zero, ?_⟩
  have he : (Projectivization.mk K v hv).rep = (a : K) • v := ha.symm
  have hi : coefficientIdeal R K M (Projectivization.mk K v hv).rep
      (Projectivization.mk K v hv).rep_nonzero =
      coefficientIdeal R K M ((a : K) • v) (smul_ne_zero a.ne_zero hv) := by
    apply FractionalIdeal.ext
    intro t
    change t • (Projectivization.mk K v hv).rep ∈ M.val ↔ t • ((a : K) • v) ∈ M.val
    rw [he]
  rw [hi, kp_cusp_coefficientIdeal_smul R K M v hv (a : K) a.ne_zero,
    ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    mul_inv_cancel₀ a.ne_zero, FractionalIdeal.spanSingleton_one, one_mul]

private theorem cusp_lineClass_map
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M N : FullLattice R K) (g : (K × K) ≃ₗ[K] (K × K))
    (hg : Submodule.map (g.toLinearMap.restrictScalars R) M.val = N.val)
    (q : RationalLine K) :
    lineClass R K N (Projectivization.map g.toLinearMap g.injective q) =
      lineClass R K M q := by
  rw [← Projectivization.mk_rep q, Projectivization.map_mk,
    kp_cusp_lineClass_mk, kp_cusp_lineClass_mk]
  congr 2
  apply FractionalIdeal.ext
  intro t
  change t • g q.rep ∈ N.val ↔ t • q.rep ∈ M.val
  rw [← hg, ← g.map_smul]
  constructor
  · rintro ⟨x, hx, he⟩
    exact g.injective he ▸ hx
  · intro ht
    exact Submodule.mem_map_of_mem ht

private theorem cusp_determinantClass_coordinates
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0)
    (v w : K × K) (hd : det₂ K v w ≠ 0)
    (hM : ∀ x : K × K, x ∈ M.val ↔
      ∃ s ∈ I, ∃ t ∈ J, x = s • v + t • w) :
    determinantClass R K M =
      ClassGroup.mk K (Units.mk0 I hI) * ClassGroup.mk K (Units.mk0 J hJ) := by
  have he : determinantIdeal R K M =
      FractionalIdeal.spanSingleton R⁰ (det₂ K v w) * (I * J) :=
    Subtype.ext (kp_cusp_determinantSubmodule_ideal_coordinates R K M.val I J hI hJ v w hd hM)
  rw [← map_mul, ← Units.mk0_mul I J (mul_ne_zero hI hJ)]
  unfold determinantClass
  apply (kp_cusp_class_eq_iff_scalar R K _ _ _ _).mpr
  refine ⟨(det₂ K v w)⁻¹, inv_ne_zero hd, ?_⟩
  rw [he, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    inv_mul_cancel₀ hd, FractionalIdeal.spanSingleton_one, one_mul]

theorem kp_cusp_lineEquivalent_iff_lineClass_eq
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (q q' : RationalLine K) :
    lineEquivalent R K M.val q q' ↔ lineClass R K M q = lineClass R K M q' := by
  classical
  constructor
  · rintro ⟨g, hg, hq⟩
    rw [← hq, cusp_lineClass_map R K M M g hg]
  · intro hq
    let v := q.rep
    let v' := q'.rep
    obtain ⟨I, J, w, hI, hJ, hIv, hd, hM, _, e, he⟩ :=
      kp_cusp_line_adapted_ideal_splitting R K M v q.rep_nonzero
    obtain ⟨I', J', w', hI', hJ', hIv', hd', hM', _, e', he'⟩ :=
      kp_cusp_line_adapted_ideal_splitting R K M v' q'.rep_nonzero
    have hCI : ClassGroup.mk K (Units.mk0 I hI) = ClassGroup.mk K (Units.mk0 I' hI') := by
      have hi : I = coefficientIdeal R K M v q.rep_nonzero := Subtype.ext hIv
      have hi' : I' = coefficientIdeal R K M v' q'.rep_nonzero := Subtype.ext hIv'
      unfold lineClass at hq
      change ClassGroup.mk K (Units.mk0 (coefficientIdeal R K M v q.rep_nonzero) _) =
        ClassGroup.mk K (Units.mk0 (coefficientIdeal R K M v' q'.rep_nonzero) _) at hq
      simpa only [← hi, ← hi'] using hq
    have hCJ : ClassGroup.mk K (Units.mk0 J hJ) = ClassGroup.mk K (Units.mk0 J' hJ') := by
      have h₁ := cusp_determinantClass_coordinates R K M I J hI hJ v w hd hM
      have h₂ := cusp_determinantClass_coordinates R K M I' J' hI' hJ' v' w' hd' hM'
      rw [hCI] at h₁
      exact mul_left_cancel (h₁.symm.trans h₂)
    obtain ⟨eI⟩ := (kp_cusp_fractional_ideal_equiv_iff R K I I' hI hI').mpr
      ((kp_cusp_class_eq_iff_scalar R K I I' hI hI').mp hCI)
    obtain ⟨eJ⟩ := (kp_cusp_fractional_ideal_equiv_iff R K J J' hJ hJ').mpr
      ((kp_cusp_class_eq_iff_scalar R K J J' hJ hJ').mp hCJ)
    let f := (e.symm.trans (eI.prodCongr eJ)).trans e'
    letI : Submodule.IsLattice K M.val := M.property
    obtain ⟨g, ⟨hg, hgM⟩, _⟩ :=
      kp_cusp_full_lattice_equiv_extension R K (K × K) (K × K) M.val M.val f
    refine ⟨g, hgM, ?_⟩
    have hIb : I.val ≠ ⊥ := by
      intro h
      apply hI
      apply Subtype.ext
      exact h.trans FractionalIdeal.coe_zero.symm
    obtain ⟨t, ht, ht0⟩ := (Submodule.ne_bot_iff I.val).mp hIb
    let s : I := ⟨t, ht⟩
    have htv : t • v ≠ 0 := smul_ne_zero ht0 q.rep_nonzero
    have hsi : (eI s : K) ≠ 0 := by
      intro hz
      have hsz : eI s = 0 := Subtype.ext hz
      have hs : s = (0 : I.val) := eI.injective (hsz.trans (map_zero eI).symm)
      exact ht0 (congrArg Subtype.val hs)
    have hgv : g (t • v) = (eI s : K) • v' := by
      have h := hg (e (s, (0 : J.val)))
      have hleft : (e (s, (0 : J.val)) : K × K) = t • v := by simpa using he s (0 : J.val)
      have hright : (f (e (s, (0 : J.val))) : K × K) = (eI s : K) • v' := by
        simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
          LinearEquiv.prodCongr_apply, map_zero]
        have hz : eJ (0 : J.val) = (0 : J'.val) := map_zero eJ
        rw [hz]
        simpa using he' (eI s) (0 : J'.val)
      rwa [hleft, hright] at h
    have hqv : Projectivization.mk K (t • v) htv = q := by
      rw [← Projectivization.mk_rep q]
      apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
      exact ⟨Units.mk0 t ht0, rfl⟩
    rw [← hqv, Projectivization.map_mk, ← Projectivization.mk_rep q']
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    exact ⟨Units.mk0 (eI s : K) hsi, hgv.symm⟩

private theorem cusp_coordinate_isLattice
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) :
    Submodule.IsLattice K (coordinateLattice R K I J) := by
  have hn : ∀ L : FractionalIdeal R⁰ K, L ≠ 0 → ∃ t ∈ L, t ≠ (0 : K) := by
    intro L hL
    apply (Submodule.ne_bot_iff L.val).mp
    intro h
    exact hL (Subtype.ext (h.trans FractionalIdeal.coe_zero.symm))
  obtain ⟨s, hs, hs0⟩ := hn I hI
  obtain ⟨t, ht, ht0⟩ := hn J hJ
  refine ⟨(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).prod
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl J), ?_⟩
  apply top_unique
  intro x _
  have h₁ : ((s, 0) : K × K) ∈ coordinateLattice R K I J :=
    ⟨hs, Submodule.zero_mem _⟩
  have h₂ : ((0, t) : K × K) ∈ coordinateLattice R K I J :=
    ⟨Submodule.zero_mem _, ht⟩
  have he : x = (x.1 / s) • (s, 0) + (x.2 / t) • (0, t) := by
    ext <;> simp [hs0, ht0]
  rw [he]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span h₁))
    (Submodule.smul_mem _ _ (Submodule.subset_span h₂))

theorem kp_cusp_lineClass_surjective
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    Function.Surjective (lineClass R K M) := by
  classical
  intro c
  refine ClassGroup.induction K (fun U => ?_) c
  let I : FractionalIdeal R⁰ K := U.val
  have hI : I ≠ 0 := U.ne_zero
  let D := determinantIdeal R K M
  have hD : D ≠ 0 := by
    intro h
    apply kp_cusp_determinantSubmodule_ne_bot R K M
    exact (congrArg Subtype.val h).trans FractionalIdeal.coe_zero
  let J := D * I⁻¹
  have hJ : J ≠ 0 := mul_ne_zero hD (inv_ne_zero hI)
  let N : FullLattice R K :=
    ⟨coordinateLattice R K I J, cusp_coordinate_isLattice R K I J hI hJ⟩
  have hNI : determinantIdeal R K N = D := by
    have h₁ := kp_cusp_determinantSubmodule_coordinateLattice R K I J
    apply Subtype.ext
    change determinantSubmodule R K (coordinateLattice R K I J) = D.val
    rw [h₁]
    have he : I * J = D := by
      dsimp [J]
      rw [mul_comm D, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
    rw [he]
  have hNC : determinantClass R K N = determinantClass R K M := by
    unfold determinantClass
    congr 1
    exact Units.ext hNI
  obtain ⟨g, hg⟩ := (kp_cusp_latticeEquivalent_iff_determinantClass_eq R K N M).mpr hNC
  have hv : ((1, 0) : K × K) ≠ 0 := by simp
  let q := Projectivization.mk K ((1, 0) : K × K) hv
  refine ⟨Projectivization.map g.toLinearMap g.injective q, ?_⟩
  rw [cusp_lineClass_map R K N M g hg, kp_cusp_lineClass_mk]
  have hcoeff : coefficientIdeal R K N ((1, 0) : K × K) hv = I := by
    apply FractionalIdeal.ext
    intro t
    change t • ((1, 0) : K × K) ∈ coordinateLattice R K I J ↔ t ∈ I
    simp [coordinateLattice, Submodule.mem_prod]
  congr 1
  exact Units.ext hcoeff

theorem kp_cusp_lineOrbit_classGroup_equiv
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    ∃ e : Quotient (lineSetoid R K M.val) ≃ ClassGroup R,
      ∀ q : RationalLine K,
        e (Quotient.mk (lineSetoid R K M.val) q) = lineClass R K M q := by
  classical
  let f : Quotient (lineSetoid R K M.val) → ClassGroup R :=
    Quotient.lift (lineClass R K M) (fun q q' h =>
      (kp_cusp_lineEquivalent_iff_lineClass_eq R K M q q').mp h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro q q' h
      exact Quotient.sound ((kp_cusp_lineEquivalent_iff_lineClass_eq R K M q q').mpr h)
    · intro c
      obtain ⟨q, hq⟩ := kp_cusp_lineClass_surjective R K M c
      exact ⟨Quotient.mk _ q, hq⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

theorem kp_cusp_numberField_finite_lineOrbits
    (F : Type*) [Field F] [NumberField F]
    (M : FullLattice (NumberField.RingOfIntegers F) F) :
    Finite (Quotient (lineSetoid (NumberField.RingOfIntegers F) F M.val)) := by
  obtain ⟨e, _⟩ := kp_cusp_lineOrbit_classGroup_equiv (NumberField.RingOfIntegers F) F M
  exact Finite.of_injective e e.injective

end DedekindZetaZeroFree
