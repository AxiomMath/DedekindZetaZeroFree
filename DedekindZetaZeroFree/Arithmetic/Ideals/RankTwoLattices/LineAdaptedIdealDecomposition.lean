module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Lattices.LocalizationAndMapExtension
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

theorem kp_cusp_coefficientSubmodule_fg
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) :
    (coefficientSubmodule R K M.val v).FG := by
  let f := (LinearMap.toSpanSingleton K (K × K) v).restrictScalars R
  apply Submodule.fg_of_fg_map_injective f (smul_left_injective K hv)
  apply Submodule.FG.of_le M.property.fg
  rintro x ⟨t, ht, rfl⟩
  exact ht

theorem kp_cusp_coefficientSubmodule_isFractional
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) :
    IsFractional R⁰ (coefficientSubmodule R K M.val v) := by
  exact FractionalIdeal.isFractional_of_fg (kp_cusp_coefficientSubmodule_fg R K M v hv)

theorem kp_cusp_coefficientSubmodule_ne_bot
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) :
    coefficientSubmodule R K M.val v ≠ ⊥ := by
  letI : Submodule.IsLattice K M.val := M.property
  obtain ⟨r, hr, hrv⟩ := kp_cusp_full_lattice_clear_denominators R K (K × K) M.val v
  intro h
  have hm : algebraMap R K r ∈ coefficientSubmodule R K M.val v := hrv
  rw [h, Submodule.mem_bot] at hm
  exact hr ((IsFractionRing.injective R K) (by simpa using hm))

private theorem det_zero_coeff
    {K : Type*} [Field K] (v x : K × K) (hv : v ≠ 0)
    (h : det₂ K v x = 0) : ∃ s : K, x = s • v := by
  by_cases h₁ : v.1 = 0
  · have h₂ : v.2 ≠ 0 := by
      intro h₂
      exact hv (Prod.ext h₁ h₂)
    have hx : x.1 = 0 := by
      have hh : v.2 * x.1 = 0 := by simpa [det₂, h₁] using h
      exact (mul_eq_zero.mp hh).resolve_left h₂
    refine ⟨x.2 / v.2, Prod.ext ?_ ?_⟩
    · simp [hx, h₁]
    · simp [smul_eq_mul, h₂]
  · refine ⟨x.1 / v.1, Prod.ext ?_ ?_⟩
    · simp [smul_eq_mul, h₁]
    · change x.2 = (x.1 / v.1) * v.2
      rw [div_mul_eq_mul_div, eq_div_iff h₁]
      have hh := sub_eq_zero.mp h
      change v.1 * x.2 = v.2 * x.1 at hh
      simpa [mul_comm] using hh

theorem kp_cusp_line_adapted_ideal_splitting
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) :
    ∃ (I J : FractionalIdeal R⁰ K) (w : K × K),
      I ≠ 0 ∧ J ≠ 0 ∧
      I.val = coefficientSubmodule R K M.val v ∧
      det₂ K v w ≠ 0 ∧
      (∀ x : K × K, x ∈ M.val ↔
        ∃ s ∈ I, ∃ t ∈ J, x = s • v + t • w) ∧
      Module.Projective R J ∧
      ∃ e : (I × J) ≃ₗ[R] M.val,
        ∀ (s : I) (t : J), (e (s, t)).val = s.val • v + t.val • w := by
  classical
  letI : Submodule.IsLattice K M.val := M.property
  let p : (K × K) →ₗ[K] K :=
    { toFun := det₂ K v
      map_add' := by intro x y; simp [det₂]; ring
      map_smul' := by intro a x; simp [det₂, smul_eq_mul]; ring }
  have pv : p v = 0 := by dsimp [p, det₂]; ring
  obtain ⟨u, hu⟩ : ∃ u : K × K, p u ≠ 0 := by
    by_cases h₁ : v.1 = 0
    · refine ⟨(1, 0), ?_⟩
      have h₂ : v.2 ≠ 0 := by
        intro h₂; exact hv (Prod.ext h₁ h₂)
      simpa [p, det₂] using h₂
    · exact ⟨(0, 1), by simpa [p, det₂] using h₁⟩
  let q : M.val →ₗ[R] K := (p.restrictScalars R).comp M.val.subtype
  have hfg : q.range.FG := by
    rw [LinearMap.range_comp]
    simpa using M.property.fg.map (p.restrictScalars R)
  let I : FractionalIdeal R⁰ K :=
    ⟨coefficientSubmodule R K M.val v, kp_cusp_coefficientSubmodule_isFractional R K M v hv⟩
  let J : FractionalIdeal R⁰ K := ⟨q.range, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := by
    intro h
    exact kp_cusp_coefficientSubmodule_ne_bot R K M v hv
      (by simpa only [I, FractionalIdeal.coe_mk, FractionalIdeal.coe_zero] using congrArg (fun L : FractionalIdeal R⁰ K => (L : Submodule R K)) h)
  have hJ : J ≠ 0 := by
    obtain ⟨r, hr, hru⟩ := kp_cusp_full_lattice_clear_denominators R K (K × K) M.val u
    have hp : p ((algebraMap R K r) • u) ≠ 0 := by
      rw [map_smul, smul_eq_mul]
      exact mul_ne_zero (by intro hh; exact hr ((IsFractionRing.injective R K) (by simpa using hh))) hu
    intro h
    have hm : p ((algebraMap R K r) • u) ∈ J.val := ⟨⟨_, hru⟩, rfl⟩
    rw [h] at hm
    exact hp ((FractionalIdeal.mem_zero_iff R⁰).mp hm)
  letI : Module.Finite R J := Module.Finite.of_fg hfg
  letI : Module.FinitePresentation R J := Module.finitePresentation_of_finite R J
  letI : Module.Projective R J := Module.Flat.projective_of_finitePresentation
  let π : M.val →ₗ[R] J := q.rangeRestrict
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π (LinearMap.id : J →ₗ[R] J)
    q.surjective_rangeRestrict
  have hσp (t : J) : p (σ t).val = t.val :=
    congrArg Subtype.val (LinearMap.congr_fun hσ t)
  let σ₁ : J →ₗ[R] K := (LinearMap.fst R K K).comp (M.val.subtype.comp σ)
  let σ₂ : J →ₗ[R] K := (LinearMap.snd R K K).comp (M.val.subtype.comp σ)
  obtain ⟨a, ha, _⟩ := kp_cusp_fractional_ideal_map_scalar R K J hJ σ₁
  obtain ⟨b, hb, _⟩ := kp_cusp_fractional_ideal_map_scalar R K J hJ σ₂
  let w : K × K := (a, b)
  have hσw (t : J) : (σ t).val = t.val • w := by
    apply Prod.ext
    · simpa [σ₁, w, smul_eq_mul, mul_comm] using ha t
    · simpa [σ₂, w, smul_eq_mul, mul_comm] using hb t
  have hpw : p w = 1 := by
    have hnb : J.val ≠ ⊥ := by
      intro h
      exact hJ (FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm))
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    have hh := hσp ⟨t, ht⟩
    rw [hσw, map_smul, smul_eq_mul] at hh
    exact (mul_left_cancel₀ ht0 (hh.trans (mul_one t).symm))
  let f : (I × J) →ₗ[R] M.val :=
    { toFun := fun st => ⟨st.1.val • v + (σ st.2).val,
        M.val.add_mem st.1.property (σ st.2).property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul, map_add]
        abel
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
          smul_add, smul_assoc, RingHom.id_apply] }
  have hfval (s : I) (t : J) : (f (s,t)).val = s.val • v + t.val • w := by
    dsimp [f]
    rw [hσw]
  have hpf (st : I × J) : p (f st).val = st.2.val := by
    rw [hfval, map_add, map_smul, map_smul, pv, hpw]
    simp
  have hfinj : Function.Injective f := by
    intro x y h
    have ht : x.2 = y.2 := Subtype.ext (by
      simpa only [hpf] using congrArg (fun z : M.val => p z.val) h)
    apply Prod.ext _ ht
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    rw [hfval, hfval, ht] at hh
    exact smul_left_injective K hv (add_right_cancel hh)
  have hfsurj : Function.Surjective f := by
    intro x
    let t : J := π x
    have hpz : p (x.val - (σ t).val) = 0 := by
      rw [map_sub, hσp]
      exact sub_self _
    obtain ⟨s, hs⟩ := det_zero_coeff v (x.val - (σ t).val) hv hpz
    have hsm : s • v ∈ M.val := by
      rw [← hs]
      exact M.val.sub_mem x.property (σ t).property
    refine ⟨(⟨s, hsm⟩, t), Subtype.ext ?_⟩
    change s • v + (σ t).val = x.val
    rw [← hs, sub_add_cancel]
  refine ⟨I, J, w, hI, hJ, rfl, ?_, ?_, inferInstance,
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, hfval⟩
  · change p w ≠ 0
    rw [hpw]
    exact one_ne_zero
  · intro x
    constructor
    · intro hx
      obtain ⟨⟨s,t⟩, hst⟩ := hfsurj ⟨x,hx⟩
      exact ⟨s.val, s.property, t.val, t.property,
        (congrArg Subtype.val hst).symm.trans (hfval s t)⟩
    · rintro ⟨s, hs, t, ht, rfl⟩
      rw [← hfval ⟨s,hs⟩ ⟨t,ht⟩]
      exact (f (⟨s,hs⟩, ⟨t,ht⟩)).property

end DedekindZetaZeroFree
