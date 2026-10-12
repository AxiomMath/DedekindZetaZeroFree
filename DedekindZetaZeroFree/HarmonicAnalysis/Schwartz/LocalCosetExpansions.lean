module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules
public import DedekindZetaZeroFree.Adeles.Characters.LocalAdditiveCharacterSmoothness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPJacquetStepFunction

open MeasureTheory
open scoped Topology

def CcLC (K E : Type*) [TopologicalSpace K] [AddCommGroup E] [Module ℂ E] :
    Submodule ℂ (LocallyConstant K E) where
  carrier := {φ | HasCompactSupport (φ : K → E)}
  zero_mem' := HasCompactSupport.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c φ hf => hf.smul_left (f := fun _ => c)

def value {K E : Type*} [TopologicalSpace K] [AddCommGroup E] [Module ℂ E]
    (φ : CcLC K E) (x : K) : E := φ.val x

def additiveCoset {K : Type*} [AddCommGroup K] (H : AddSubgroup K) (a : K) : Set K :=
  {x | x - a ∈ H}

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

private theorem small_level (O : Set K) (hO : O ∈ nhds (0 : K)) :
    ∃ J : AddSubgroup K, IsOpen (J : Set K) ∧ IsCompact (J : Set K) ∧
      (J : Set K) ⊆ O := by
  obtain ⟨γ, _, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp hO
  obtain ⟨t, ht0, ht⟩ := Valuation.IsNontrivial.exists_lt_one
    (v := ValuativeRel.valuation K)
  let β := (γ : ValuativeRel.ValueGroupWithZero K) * ValuativeRel.valuation K t
  have hβ0 : β ≠ 0 := mul_ne_zero (Units.ne_zero γ) (by simpa using ht0)
  have hβγ : β < (γ : ValuativeRel.ValueGroupWithZero K) := by
    simpa [β] using mul_lt_mul_of_pos_left ht (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  let J := (ValuativeRel.valuation K).leAddSubgroup β
  have hJopen : IsOpen (J : Set K) := by
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective β
    change IsOpen {x | ValuativeRel.valuation K x ≤ β}
    rw [← ha]
    simp_rw [← (ValuativeRel.valuation K).restrict_le_iff]
    apply Valuation.isOpen_closedBall
    simpa [← ha] using hβ0
  exact ⟨J, hJopen, IsNonarchimedeanLocalField.isCompact_closedBall K β,
    fun j hj => hγ (hj.trans_lt hβγ)⟩

theorem exists_compactOpen_translation_level (φ : CcLC K E)
    (U : AddSubgroup K) (hUopen : IsOpen (U : Set K))
    (hUcompact : IsCompact (U : Set K)) :
    ∃ H : AddSubgroup K, H ≤ U ∧ IsOpen (H : Set K) ∧
      IsCompact (H : Set K) ∧
      ∀ x : K, ∀ h ∈ H, value φ (x + h) = value φ x := by
  classical
  have hb (x : K) : ∃ B : AddSubgroup K, IsOpen (B : Set K) ∧
      ∀ y, y - x ∈ B → value φ y = value φ x := by
    have hn : {h : K | value φ (x + h) = value φ x} ∈ nhds 0 := by
      have ht : Filter.Tendsto (fun h : K => x + h) (nhds 0) (nhds x) := by
        simpa only [add_zero, id_eq] using
          (tendsto_const_nhds : Filter.Tendsto (fun _ : K => x) (nhds 0) (nhds x)).add
            (Filter.tendsto_id : Filter.Tendsto (fun h : K => h) (nhds 0) (nhds 0))
      exact ht.eventually (φ.val.isLocallyConstant.eventually_eq x)
    obtain ⟨B, hBo, _, hB⟩ := small_level _ hn
    exact ⟨B, hBo, fun y hy => by simpa using hB hy⟩
  choose B hBo hB using hb
  have hc (x : K) : IsOpen (additiveCoset (B x) x) :=
    (hBo x).preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := φ.property.elim_finite_subcover
    (fun x => additiveCoset (B x) x) hc (fun x _ =>
      Set.mem_iUnion.mpr ⟨x, by simp [additiveCoset]⟩)
  let O : Set K := (U : Set K) ∩ ⋂ x ∈ t, (B x : Set K)
  have hOo : IsOpen O := hUopen.inter (isOpen_biInter_finset fun x _ => hBo x)
  have hO0 : (0 : K) ∈ O := by simp [O]
  obtain ⟨H, hHo, hHc, hHO⟩ := small_level O (hOo.mem_nhds hO0)
  have hlev (x : K) (hx : x ∈ tsupport (φ.val : K → E)) (h : K) (hh : h ∈ H) :
      value φ (x + h) = value φ x := by
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hha : h ∈ B a := Set.mem_iInter₂.mp (hHO hh).2 a hat
    have hxa' : x - a ∈ B a := hxa
    have hxh : (x + h) - a ∈ B a := by
      simpa only [add_sub_right_comm] using (B a).add_mem hxa' hha
    exact (hB a _ hxh).trans (hB a _ hxa').symm
  refine ⟨H, fun h hh => (hHO hh).1, hHo, hHc, ?_⟩
  intro x h hh
  by_cases hx : x ∈ tsupport (φ.val : K → E)
  · exact hlev x hx h hh
  by_cases hxh : x + h ∈ tsupport (φ.val : K → E)
  · simpa using (hlev (x + h) hxh (-h) (H.neg_mem hh)).symm
  · have hx0 := image_eq_zero_of_notMem_tsupport hx
    have hxh0 := image_eq_zero_of_notMem_tsupport hxh
    exact hxh0.trans hx0.symm

theorem finite_coset_expansion (φ : CcLC K E) (H : AddSubgroup K)
    (hHopen : IsOpen (H : Set K)) (hHcompact : IsCompact (H : Set K))
    (hφ : ∀ x : K, ∀ h ∈ H, value φ (x + h) = value φ x) :
    ∃ (n : ℕ) (a : Fin n → K) (e : Fin n → E),
      Function.Injective (fun i => QuotientAddGroup.mk' H (a i)) ∧
      (∀ x : K, value φ x =
        ∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) := by
  classical
  letI : DiscreteTopology (K ⧸ H) := QuotientAddGroup.discreteTopology hHopen
  let S : Set (K ⧸ H) := QuotientAddGroup.mk' H '' tsupport (φ.val : K → E)
  have hS : S.Finite := (φ.property.image QuotientAddGroup.continuous_mk).finite_of_discrete
  letI : Fintype S := hS.fintype
  let a : S → K := fun q => Quotient.out q.val
  have ha (q : S) : QuotientAddGroup.mk' H (a q) = q.val := Quotient.out_eq q.val
  have hmem (q : S) (x : K) : x ∈ additiveCoset H (a q) ↔
      QuotientAddGroup.mk' H x = q.val := by
    change x - a q ∈ H ↔ _
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    change QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H (a q) ↔ _
    rw [ha]
  have hv (q : S) (x : K) (hx : x ∈ additiveCoset H (a q)) :
      value φ x = value φ (a q) := by
    simpa using hφ (a q) (x - a q) hx
  have hex (x : K) : value φ x =
      ∑ q : S, (additiveCoset H (a q)).indicator (fun _ => value φ (a q)) x := by
    by_cases hx : QuotientAddGroup.mk' H x ∈ S
    · let q : S := ⟨QuotientAddGroup.mk' H x, hx⟩
      rw [Finset.sum_eq_single q]
      · rw [Set.indicator_of_mem ((hmem q x).mpr rfl)]
        exact hv q x ((hmem q x).mpr rfl)
      · intro b _ hb
        apply Set.indicator_of_notMem
        intro hm
        apply hb
        apply Subtype.ext
        exact ((hmem b x).mp hm).symm
      · simp
    · have hx0 : value φ x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact hx ⟨x, hm, rfl⟩
      rw [hx0]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro hm
      exact hx (((hmem q x).mp hm).symm ▸ q.property)
  let r : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, a ∘ r, (fun q => value φ (a q)) ∘ r, ?_, ?_⟩
  · intro i j hij
    apply r.injective
    apply Subtype.ext
    simpa only [Function.comp_apply, ha] using hij
  · intro x
    rw [hex]
    exact (r.sum_comp (fun q =>
      (additiveCoset H (a q)).indicator (fun _ => value φ (a q)) x)).symm

private theorem compact_character_unitary
    (U : AddSubgroup K) (hUc : IsCompact (U : Set K))
    (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ) (u : K) (hu : u ∈ U) :
    ‖(ψ (Multiplicative.ofAdd u) : ℂ)‖ = 1 := by
  have hc : Continuous (fun x : K => (ψ (Multiplicative.ofAdd x) : ℂ)) :=
    Units.continuous_val.comp (hψ.comp continuous_ofAdd)
  obtain ⟨C, hC⟩ := (hUc.image hc).isBounded.exists_norm_le
  have hle (x : K) (hx : x ∈ U) : ‖(ψ (Multiplicative.ofAdd x) : ℂ)‖ ≤ 1 := by
    by_contra hn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge hn)
    have hb := hC _ ⟨n • x, U.nsmul_mem hx n, rfl⟩
    have hp : ψ (Multiplicative.ofAdd (n • x)) = ψ (Multiplicative.ofAdd x) ^ n := by
      rw [ofAdd_nsmul, map_pow]
    change ‖(ψ (Multiplicative.ofAdd (n • x)) : ℂ)‖ ≤ C at hb
    rw [hp, Units.val_pow_eq_pow_val, norm_pow] at hb
    exact (not_lt_of_ge hb) hn
  have hi := hle (-u) (U.neg_mem hu)
  have hp : ψ (Multiplicative.ofAdd (-u)) = (ψ (Multiplicative.ofAdd u))⁻¹ := by
    rw [ofAdd_neg, map_inv]
  rw [hp, Units.val_inv_eq_inv_val, norm_inv] at hi
  have hn : 0 < ‖(ψ (Multiplicative.ofAdd u) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  exact le_antisymm (hle u hu) ((inv_le_one₀ hn).mp hi)

theorem exists_character_adapted_expansion (φ : CcLC K E)
    (U : AddSubgroup K) (hUopen : IsOpen (U : Set K))
    (hUcompact : IsCompact (U : Set K))
    (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ) :
    ∃ H : AddSubgroup K, H ≤ U ∧ IsOpen (H : Set K) ∧
      IsCompact (H : Set K) ∧
      (∀ h ∈ H, ψ (Multiplicative.ofAdd h) = 1) ∧
      (∀ x : K, ∀ h ∈ H, value φ (x + h) = value φ x) ∧
      ∃ (n : ℕ) (a : Fin n → K) (e : Fin n → E),
        Function.Injective (fun i => QuotientAddGroup.mk' H (a i)) ∧
        (∀ x : K, value φ x =
          ∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) := by
  classical
  let c : U → Circle := fun u => ⟨(ψ (Multiplicative.ofAdd (u : K)) : ℂ),
    mem_sphere_zero_iff_norm.mpr (compact_character_unitary U hUcompact ψ hψ u u.property)⟩
  have hc : Continuous c :=
    ((Units.continuous_val.comp (hψ.comp continuous_ofAdd)).comp continuous_subtype_val).subtype_mk _
  have hc0 : c 0 = 1 := by
    apply Subtype.ext
    simp [c]
  have hn : c ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ nhds (0 : U) := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (Circle.isOpen_centeredArc _).mem_nhds
    rw [hc0, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rw [nhds_subtype] at hn
  obtain ⟨O, hO, hOc⟩ := Filter.mem_comap.mp hn
  obtain ⟨J, hJo, hJc, hJO⟩ := small_level ((U : Set K) ∩ O)
    (Filter.inter_mem (hUopen.mem_nhds U.zero_mem) hO)
  have hJU : J ≤ U := fun j hj => (hJO hj).1
  have hψJ (j : K) (hj : j ∈ J) : ψ (Multiplicative.ofAdd j) = 1 := by
    have he : c ⟨j, hJU hj⟩ = 1 := by
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro n hn
      have hnj := J.nsmul_mem hj n
      have hh := hOc (show (⟨n • j, hJU hnj⟩ : U) ∈ Subtype.val ⁻¹' O from (hJO hnj).2)
      have hp : c ⟨n • j, hJU hnj⟩ = c ⟨j, hJU hj⟩ ^ n := by
        apply Subtype.ext
        change (ψ (Multiplicative.ofAdd (n • j)) : ℂ) =
          (ψ (Multiplicative.ofAdd j) : ℂ) ^ n
        rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]
      change c ⟨n • j, hJU hnj⟩ ∈ Circle.centeredArc (Real.pi / 2) at hh
      rwa [hp] at hh
    apply Units.ext
    exact congrArg (fun z : Circle => (z : ℂ)) he
  obtain ⟨H, hHJ, hHo, hHc, hφH⟩ := exists_compactOpen_translation_level φ J hJo hJc
  exact ⟨H, hHJ.trans hJU, hHo, hHc, fun h hh => hψJ h (hHJ hh), hφH,
    finite_coset_expansion φ H hHo hHc hφH⟩

variable [MeasurableSpace K] [BorelSpace K]

theorem compactOpen_volume_pos_lt_top (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K)) :
    0 < μ (H : Set K) ∧ μ (H : Set K) < ⊤ := by
  exact ⟨hHopen.measure_pos μ ⟨0, H.zero_mem⟩, hHcompact.measure_lt_top⟩

end LocalField

section Integrability

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem integrable (φ : CcLC K E) (μ : Measure K) [μ.IsAddHaarMeasure] :
    Integrable (value φ) μ := by
  exact φ.val.continuous.integrable_of_hasCompactSupport φ.property

theorem integrable_inverse_character_smul (φ : CcLC K E)
    (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure K) [μ.IsAddHaarMeasure] :
    Integrable (fun x => ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) • value φ x) μ := by
  have hc : Continuous (fun x : K => ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹)) := by
    simpa only [Function.comp_def, Pi.inv_apply, Units.val_inv_eq_inv_val] using
      ((Units.continuous_val.comp (hψ.inv)).comp continuous_ofAdd)
  exact (hc.smul φ.val.continuous).integrable_of_hasCompactSupport
    (φ.property.smul_left (f := fun x => ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹)))

end Integrability

end DedekindZetaZeroFree.KPJacquetStepFunction

end
