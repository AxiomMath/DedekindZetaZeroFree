module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PrimaryAngularNormPhases
public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderClassCharacters
public import DedekindZetaZeroFree.LFunctions.Hecke.EisensteinAngularFractionalCharacter
public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation

@[expose] public section

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic

noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

 abbrev e (A : SArithmeticData F) := ClassCharacterGluing.exteriorFractionalUnit A
 def prod (A : SArithmeticData F) (I J : A.Exterior) : A.Exterior :=
  ⟨I.val * J.val, mul_ne_zero I.property.1 J.property.1,
    by rw [Ideal.mul_sup_eq_of_coprime_left I.property.2]; exact J.property.2⟩
 def unitIdeal (A : SArithmeticData F) : A.Exterior := ⟨⊤, by simp⟩
private lemma e_inj (A : SArithmeticData F) : Function.Injective (e A) := by
  intro I J h
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  apply (FractionalIdeal.coeIdeal_inj (K := F)).mp
  simpa only [e, ClassCharacterGluing.exteriorFractionalUnit_val, A.exteriorIdealEquiv_apply] using congrArg Units.val h
private lemma e_prod (A : SArithmeticData F) (I J : A.Exterior) :
    e A (prod A I J) = e A I * e A J :=
  ClassCharacterGluing.exteriorFractionalUnit_mul A I J _ rfl
private lemma e_unit (A : SArithmeticData F) : e A (unitIdeal A) = 1 := by
  apply Units.ext
  rw [e, ClassCharacterGluing.exteriorFractionalUnit_val]
  simp [SArithmeticData.extendIdeal, unitIdeal, Ideal.map_top]
private lemma e_ratio (A : SArithmeticData F) (K : (FractionalIdeal A.R⁰ F)ˣ) :
    ∃ I J : A.Exterior, K = e A I / e A J := by
  let k : FractionalIdeal A.R⁰ F := K
  have hn : k.num ≠ ⊥ := by
    intro h
    exact K.ne_zero (FractionalIdeal.num_eq_zero_iff.mp h)
  let d : Ideal A.R := Ideal.span {(k.den : A.R)}
  have hd : d ≠ ⊥ := by
    simpa [d, Ideal.span_singleton_eq_bot] using nonZeroDivisors.coe_ne_zero k.den
  let I := A.exteriorIdealEquiv.symm ⟨k.num, hn⟩
  let J := A.exteriorIdealEquiv.symm ⟨d, hd⟩
  have hI : A.extendIdeal I = k.num := by
    exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨k.num, hn⟩)
  have hJ : A.extendIdeal J = d := by
    exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨d, hd⟩)
  refine ⟨I, J, ?_⟩
  apply (eq_div_iff_mul_eq').mpr
  apply Units.ext
  simp only [Units.val_mul, e, ClassCharacterGluing.exteriorFractionalUnit_val, hI, hJ]
  rw [show d = Ideal.span {(k.den : A.R)} from rfl, FractionalIdeal.coeIdeal_span_singleton,
    mul_comm]
  exact k.den_mul_self_eq_num'
 def phase (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ)
    (I : A.Exterior) : Circle :=
  ⟨DHCubic.lambda F A ι I.val, by
    change DHCubic.lambda F A ι I.val ∈ Metric.sphere 0 1
    simpa [DHCubic.lambda] using DHCubic.lambdaF_exterior_norm (DHCubic.E0 F A) F A ι I⟩
private lemma phase_prod (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ)
    (I J : A.Exterior) : phase A ι (prod A I J) = phase A ι I * phase A ι J := by
  apply Subtype.ext
  exact DHCubic.lambdaF_mul (DHCubic.E0 F A) F ι I.val J.val
private lemma phase_unit (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ) :
    phase A ι (unitIdeal A) = 1 := by
  have h : prod A (unitIdeal A) (unitIdeal A) = unitIdeal A := by
    apply Subtype.ext
    simp [prod, unitIdeal, Ideal.mul_top]
  have hh := phase_prod A ι (unitIdeal A) (unitIdeal A)
  rw [h] at hh
  exact (mul_left_cancel (hh.symm.trans (mul_one _).symm))
private lemma phase_ratio_eq (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ)
    (I J I' J' : A.Exterior) (h : e A I / e A J = e A I' / e A J') :
    phase A ι I / phase A ι J = phase A ι I' / phase A ι J' := by
  apply (div_eq_div_iff_mul_eq_mul).mpr
  have he : prod A I J' = prod A I' J := e_inj A (by
    rw [e_prod, e_prod]
    exact (div_eq_div_iff_mul_eq_mul).mp h)
  rw [← phase_prod, ← phase_prod, he]

theorem exists_fractional_ideal_character (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) :
    ∃! κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle,
      ∀ I : A.Exterior,
        (κ (ClassCharacterGluing.exteriorFractionalUnit A I) : ℂ) =
          DHCubic.lambda F A ι I.val := by
  let G := (FractionalIdeal A.R⁰ F)ˣ
  have hr : ∀ K : G, ∃ p : A.Exterior × A.Exterior, K = e A p.1 / e A p.2 := by
    intro K
    obtain ⟨I, J, h⟩ := e_ratio A K
    exact ⟨(I, J), h⟩
  let r (K : G) := Classical.choose (hr K)
  have rs (K : G) : K = e A (r K).1 / e A (r K).2 := Classical.choose_spec (hr K)
  let f (K : G) : Circle := phase A ι (r K).1 / phase A ι (r K).2
  have fs (K : G) (I J : A.Exterior) (h : K = e A I / e A J) :
      f K = phase A ι I / phase A ι J :=
    phase_ratio_eq A ι _ _ I J ((rs K).symm.trans h)
  let κ : G →* Circle := {
    toFun := f
    map_one' := by
      rw [fs 1 (unitIdeal A) (unitIdeal A) (by simp)]
      simp
    map_mul' := by
      intro K L
      have h : K * L = e A (prod A (r K).1 (r L).1) /
          e A (prod A (r K).2 (r L).2) := by
        rw [e_prod, e_prod, mul_div_mul_comm]
        exact congrArg₂ (· * ·) (rs K) (rs L)
      rw [fs _ _ _ h, phase_prod, phase_prod, mul_div_mul_comm] }
  have kval (I : A.Exterior) : κ (e A I) = phase A ι I := by
    change f (e A I) = _
    rw [fs _ I (unitIdeal A) (by rw [e_unit, div_one]), phase_unit, div_one]
  refine ⟨κ, (fun I => congrArg (fun z : Circle => (z : ℂ)) (kval I)), ?_⟩
  intro κ' hκ'
  apply MonoidHom.ext
  intro K
  obtain ⟨I, J, h⟩ := e_ratio A K
  rw [h, map_div, map_div, kval, kval]
  have hI : κ' (e A I) = phase A ι I := Subtype.ext (hκ' I)
  have hJ : κ' (e A J) = phase A ι J := Subtype.ext (hκ' J)
  rw [hI, hJ]

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic

end

section

open scoped NumberField Classical Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic.FiniteNormalization

noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem exists_congruence_open_subgroup
    (S : Finset (HeightOneSpectrum (𝓞 F))) (m : 𝓞 F) (hm : m ≠ 0) :
    ∃ K : OpenSubgroup ((v : {v // v ∈ S}) → (v.val.adicCompletion F)ˣ),
      ∀ a : Fˣ,
        (fun v : {v // v ∈ S} =>
          Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a) ∈ K →
        ∀ v ∈ S,
          v.valuation F (a : F) = 1 ∧
          v.valuation F (((a : F) - 1) / (m : F)) ≤ 1 := by
  have hlocal : ∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℕ,
      ∀ x : (v.adicCompletion F)ˣ,
        x ∈ RayClass.localHigherUnitGroup v n →
        Valued.v (x : v.adicCompletion F) = 1 ∧
        Valued.v (((x : v.adicCompletion F) - 1) /
          algebraMap F (v.adicCompletion F) (m : F)) ≤ 1 := by
    intro v
    have hs : IsOpen {x : v.adicCompletion F | Valued.v x = 1} := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (Valued.isOpen_sphere (v.adicCompletion F) one_ne_zero)
    have hi : IsOpen {x : v.adicCompletion F | Valued.v x ≤ 1} :=
      Valued.isOpen_integer (v.adicCompletion F)
    have hopen : IsOpen {x : (v.adicCompletion F)ˣ |
        Valued.v (x : v.adicCompletion F) = 1 ∧
        Valued.v (((x : v.adicCompletion F) - 1) /
          algebraMap F (v.adicCompletion F) (m : F)) ≤ 1} :=
      (hs.preimage Units.continuous_val).inter
        (hi.preimage ((Units.continuous_val.sub continuous_const).div_const _))
    exact RayClass.exists_localHigherUnitGroup_subset v
      (hopen.mem_nhds (by simp))
  choose n hn using hlocal
  let H : Subgroup ((v : {v // v ∈ S}) → (v.val.adicCompletion F)ˣ) :=
    Subgroup.pi Set.univ (fun v => RayClass.localHigherUnitGroup v.val (n v.val))
  have hH : IsOpen (H : Set ((v : {v // v ∈ S}) → (v.val.adicCompletion F)ˣ)) := by
    have heq : (H : Set ((v : {v // v ∈ S}) → (v.val.adicCompletion F)ˣ)) =
        ⋂ v : {v // v ∈ S},
          (fun x => x v) ⁻¹' (RayClass.localHigherUnitGroup v.val (n v.val) :
            Set (v.val.adicCompletion F)ˣ) := by
      ext x
      simp [H, Subgroup.mem_pi]
    rw [heq]
    exact isOpen_iInter_of_finite fun v =>
      (RayClass.isOpen_localHigherUnitGroup v.val (n v.val)).preimage (continuous_apply v)
  refine ⟨⟨H, hH⟩, ?_⟩
  intro a ha v hv
  have hx := hn v
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
    ((Subgroup.mem_pi Set.univ).mp ha ⟨v, hv⟩ (Set.mem_univ _))
  change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
    Valued.v ((algebraMap F (v.adicCompletion F) (a : F) - 1) /
      algebraMap F (v.adicCompletion F) (m : F)) ≤ 1 at hx
  have hmap : (algebraMap F (v.adicCompletion F) (a : F) - 1) /
      algebraMap F (v.adicCompletion F) (m : F) =
      algebraMap F (v.adicCompletion F) (((a : F) - 1) / (m : F)) := by
    simp
  rw [hmap] at hx
  simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hx

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic.FiniteNormalization

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic.FiniteNormalization

noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

 def clearingIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {r | ∃ n : 𝓞 F, x * (r : F) = (n : F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro r s ⟨n, hn⟩ ⟨p, hp⟩
    exact ⟨n + p, by simp only [map_add, map_add, mul_add, hn, hp]⟩
  smul_mem' := by
    rintro r s ⟨n, hn⟩
    refine ⟨r * n, ?_⟩
    change x * ((r * s : 𝓞 F) : F) = ((r * n : 𝓞 F) : F)
    simp only [map_mul]
    rw [← mul_assoc, mul_comm x, mul_assoc, hn]

private theorem clearing_coprime (x : F) (v : HeightOneSpectrum (𝓞 F))
    (hx : v.valuation F x ≤ 1) : clearingIdeal x ⊔ v.asIdeal = ⊤ := by
  obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  have hdmem : (d : 𝓞 F) ∈ clearingIdeal x := ⟨n, hd⟩
  have hdnot : (d : 𝓞 F) ∉ v.asIdeal := d.prop
  by_contra h
  have heq := v.isMaximal.eq_of_le h le_sup_right
  have hmem : (d : 𝓞 F) ∈ clearingIdeal x ⊔ v.asIdeal :=
    (show clearingIdeal x ≤ clearingIdeal x ⊔ v.asIdeal from le_sup_left) hdmem
  exact hdnot (Eq.mp (congrArg (fun I : Ideal (𝓞 F) => (d : 𝓞 F) ∈ I) heq.symm) hmem)

private theorem clearing_ne_bot (x : F) : clearingIdeal x ≠ ⊥ := by
  obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) x
  intro h
  have : (d : 𝓞 F) ∈ clearingIdeal x := ⟨n, hd⟩
  rw [h, Ideal.mem_bot] at this
  exact (nonZeroDivisors.ne_zero d.prop) this

private theorem nonzero_congruent (D J : Ideal (𝓞 F)) (hD : D ≠ ⊥)
    (h : D ⊔ J = ⊤) : ∃ b ∈ D, b ≠ 0 ∧ b - 1 ∈ J := by
  have h1 : (1 : 𝓞 F) ∈ D ⊔ J := by rw [h]; trivial
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  by_cases hb0 : b = 0
  · have hc1 : c = 1 := by simpa [hb0] using hbc
    have hJ : J = ⊤ := (Ideal.eq_top_iff_one J).mpr (hc1 ▸ hc)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact ⟨d, hd, hd0, by simp [hJ]⟩
  · refine ⟨b, hb, hb0, ?_⟩
    have : b - 1 = -c := by rw [← hbc]; ring
    rw [this]
    exact J.neg_mem hc

private theorem clearing_modulus_coprime (S : Finset (HeightOneSpectrum (𝓞 F)))
    (m : 𝓞 F) (hm : m ≠ 0)
    (hSm : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → v ∈ S)
    (x : F) (hx : ∀ v ∈ S, v.valuation F x ≤ 1) :
    clearingIdeal x ⊔ Ideal.span {m} = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.ne_top_iff_exists_maximal.mp h
  have hmM : m ∈ M := hle ((show Ideal.span {m} ≤ clearingIdeal x ⊔ Ideal.span {m} from le_sup_right) (Ideal.subset_span (by simp)))
  have hM0 : M ≠ ⊥ := by
    intro heq
    exact hm (Ideal.mem_bot.mp (heq ▸ hmM))
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
  have hcop := clearing_coprime x v (hx v (hSm v hmM))
  have : clearingIdeal x ⊔ v.asIdeal ≤ M := sup_le (le_trans le_sup_left hle) le_rfl
  rw [hcop] at this
  exact hM.ne_top (top_unique this)

private theorem prime_not_mem_of_congruent (S : Finset (HeightOneSpectrum (𝓞 F)))
    (m b : 𝓞 F) (hb : b - 1 ∈ Ideal.span {m} * (∏ v ∈ S, v.asIdeal)) :
    ∀ v ∈ S, b ∉ v.asIdeal := by
  intro v hv hbv
  have hp : (∏ w ∈ S, w.asIdeal) ≤ v.asIdeal := by
    exact le_trans Ideal.prod_le_inf (Finset.inf_le hv)
  have hb1 : b - 1 ∈ v.asIdeal := hp (Ideal.mul_le_right hb)
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem hbv hb1
    simpa using this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem exterior_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : 𝓞 F) (hb : ∀ v ∈ S, b ∉ v.asIdeal) :
    Ideal.span {b} ⊔ (∏ v ∈ S, v.asIdeal) = ⊤ := by
  apply Ideal.sup_prod_eq_top
  intro v hv
  by_contra h
  have heq := v.isMaximal.eq_of_le h le_sup_right
  have hmem : b ∈ Ideal.span {b} ⊔ v.asIdeal :=
    (show Ideal.span {b} ≤ Ideal.span {b} ⊔ v.asIdeal from le_sup_left) (Ideal.subset_span (by simp))
  exact hb v hv (heq.symm ▸ hmem)

theorem exists_primary_exterior_ratio
    (S : Finset (HeightOneSpectrum (𝓞 F))) (m : 𝓞 F) (hm : m ≠ 0)
    (hSm : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → v ∈ S)
    (a : Fˣ)
    (ha : ∀ v ∈ S, v.valuation F (a : F) = 1 ∧
      v.valuation F (((a : F) - 1) / (m : F)) ≤ 1) :
    ∃ α β : 𝓞 F,
      α ≠ 0 ∧ β ≠ 0 ∧
      α - 1 ∈ Ideal.span {m} ∧ β - 1 ∈ Ideal.span {m} ∧
      Ideal.span {α} ⊔ (∏ v ∈ S, v.asIdeal) = ⊤ ∧
      Ideal.span {β} ⊔ (∏ v ∈ S, v.asIdeal) = ⊤ ∧
      (a : F) = (α : F) / (β : F) := by
  let x : F := ((a : F) - 1) / (m : F)
  let D := clearingIdeal x
  let P : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal
  have hDm : D ⊔ Ideal.span {m} = ⊤ :=
    clearing_modulus_coprime S m hm hSm x (fun v hv => (ha v hv).2)
  have hDP : D ⊔ P = ⊤ :=
    Ideal.sup_prod_eq_top (fun v hv => clearing_coprime x v (ha v hv).2)
  have hDmp : D ⊔ Ideal.span {m} * P = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left hDm]
    exact hDP
  obtain ⟨β, hβD, hβ0, hβcon⟩ :=
    nonzero_congruent D (Ideal.span {m} * P) (clearing_ne_bot x) hDmp
  obtain ⟨n, hn⟩ := hβD
  let α : 𝓞 F := β + m * n
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
  have hβF : (β : F) ≠ 0 := by exact_mod_cast hβ0
  have hα : (α : F) = (a : F) * (β : F) := by
    change ((β + m * n : 𝓞 F) : F) = (a : F) * (β : F)
    simp only [map_add, map_mul]
    change (β : F) + (m : F) * (n : F) = (a : F) * (β : F)
    rw [← hn]
    dsimp [x]
    field_simp
    <;> ring
  have hα0 : α ≠ 0 := by
    intro h
    have : (α : F) = 0 := by simp [h]
    rw [hα] at this
    exact (mul_ne_zero a.ne_zero hβF) this
  have hβm : β - 1 ∈ Ideal.span {m} := Ideal.mul_le_left hβcon
  have hαm : α - 1 ∈ Ideal.span {m} := by
    have hmn : m * n ∈ Ideal.span {m} :=
      (Ideal.span {m}).mul_mem_right n (Ideal.subset_span (by simp))
    have heq : α - 1 = (β - 1) + m * n := by dsimp [α]; ring
    rw [heq]
    exact (Ideal.span {m}).add_mem hβm hmn
  have hβnot := prime_not_mem_of_congruent S m β hβcon
  have hαnot : ∀ v ∈ S, α ∉ v.asIdeal := by
    intro v hv
    apply (v.valuation_eq_one_iff_notMem (K := F)).mp
    change v.valuation F (α : F) = 1
    rw [hα, map_mul, (ha v hv).1, one_mul]
    exact (v.valuation_eq_one_iff_notMem (K := F)).mpr (hβnot v hv)
  refine ⟨α, β, hα0, hβ0, hαm, hβm, exterior_of_not_mem S α hαnot,
    exterior_of_not_mem S β hβnot, ?_⟩
  exact (eq_div_iff hβF).mpr hα.symm

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic.FiniteNormalization

end

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic

noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

namespace FiniteNormalizationTopology

open Filter Topology

variable {H G : Type*} [Group H] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem extend_dense_character (e : H →* G) (he : DenseRange e)
    (d : H →* Circle) (K : OpenSubgroup G)
    (hK : ∀ a : H, e a ∈ K → d a = 1) :
    ∃ τ : G →* Circle, Continuous τ ∧ ∀ a : H, τ (e a) = d a := by
  let q := QuotientGroup.mk' K.toSubgroup
  let f := q.comp e
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K.toSubgroup x
    have hopen : IsOpen (q ⁻¹' {q g}) := by
      exact (isOpen_discrete {q g}).preimage continuous_quotient_mk'
    have hn : (q ⁻¹' {q g}).Nonempty := ⟨g, rfl⟩
    obtain ⟨a, ha⟩ := he.exists_mem_open hopen hn
    exact ⟨a, ha⟩
  have hk : f.ker ≤ d.ker := by
    intro a ha
    apply hK a
    exact (QuotientGroup.eq_one_iff _).mp ha
  let l := MonoidHom.liftOfSurjective f hs ⟨d, hk⟩
  let τ := l.comp q
  refine ⟨τ, ?_, ?_⟩
  · exact (continuous_of_discreteTopology : Continuous l).comp
      (continuous_quotient_mk' : Continuous q)
  · intro a
    exact MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hs)
      (Function.rightInverse_surjInv hs) ⟨d, hk⟩ a

open scoped NumberField
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]

theorem finite_diagonal_dense (A : SArithmeticData F) :
    DenseRange (fun a : Fˣ => (A.diagonal a).2) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  let val : ((v : ↥A.Sf) → (v.val.adicCompletion F)ˣ) →
      ((v : ↥A.Sf) → v.val.adicCompletion F) := fun u v => (u v : v.val.adicCompletion F)
  have hv : IsOpenEmbedding val :=
    IsOpenEmbedding.piMap (fun v => IsOpenUnits.isOpenEmbedding_unitsVal)
  have hd : DenseRange (fun x : F => fun v : ↥A.Sf =>
      algebraMap F (v.val.adicCompletion F) x) := by
    have h := PoissonSFiniteDensity.diagonal_denseRange F A.Sf
    exact h.mono (by rintro x ⟨r, rfl⟩; exact ⟨(r : F), rfl⟩)
  obtain ⟨x, hx⟩ := hd.exists_mem_open (hv.isOpenMap _ hU) (hUne.image val)
  obtain ⟨u, hu, hux⟩ := hx
  by_cases hSf : A.Sf.Nonempty
  · obtain ⟨v, hv⟩ := hSf
    have hx0 : x ≠ 0 := by
      intro he
      have hh := congrFun hux ⟨v, hv⟩
      simp only [val, he, map_zero] at hh
      exact (u ⟨v, hv⟩).ne_zero hh
    refine ⟨(A.diagonal (Units.mk0 x hx0)).2, ?_, ⟨Units.mk0 x hx0, rfl⟩⟩
    convert hu using 1
    funext v
    apply Units.ext
    exact (congrFun hux v).symm
  · haveI : IsEmpty ↥A.Sf := ⟨fun v => hSf ⟨v.val, v.property⟩⟩
    obtain ⟨u, hu⟩ := hUne
    refine ⟨(A.diagonal (1 : Fˣ)).2, ?_, ⟨1, rfl⟩⟩
    convert hu using 1

end FiniteNormalizationTopology
 def infinityDiagonal (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ)
    (w : InfinitePlace F) : Fˣ →* Circle :=
  if w.embedding.comp (algebraMap (DHCubic.E0 F A) F) = ι then
    Eisenstein.archimedeanAngular.comp (Units.map w.embedding.toMonoidHom)
  else (Eisenstein.archimedeanAngular.comp (Units.map w.embedding.toMonoidHom))⁻¹
private theorem infinityDiagonal_apply (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) (w : InfinitePlace F) (a : Fˣ) :
    (infinityDiagonal A ι w a : ℂ) =
      DHCubic.infinityComponent (DHCubic.E0 F A) F ι w (w.embedding (a : F)) := by
  unfold infinityDiagonal DHCubic.infinityComponent
  split_ifs
  · rfl
  · rw [DHCubic.star_angular _ ((map_ne_zero w.embedding).mpr a.ne_zero), zpow_neg_one]
    rfl
 def infinityDiagonalProduct (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) : Fˣ →* Circle :=
  ∏ w : InfinitePlace F, infinityDiagonal A ι w
private theorem infinityDiagonalProduct_apply (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) (a : Fˣ) :
    (infinityDiagonalProduct A ι a : ℂ) =
      ∏ w : InfinitePlace F,
        DHCubic.infinityComponent (DHCubic.E0 F A) F ι w (w.embedding (a : F)) := by
  change Circle.coeHom ((∏ w : InfinitePlace F, infinityDiagonal A ι w) a) = _
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_congr rfl (fun w _ => infinityDiagonal_apply A ι w a)

def principalDiscrepancy (A : SArithmeticData F) (ι : DHCubic.E0 F A →+* ℂ) :
    Fˣ →* Circle :=
  ((Classical.choose (exists_fractional_ideal_character A ι).exists).comp
    (ClassCharacterSteps.principalIdealMap A)) * (infinityDiagonalProduct A ι)⁻¹

theorem principalDiscrepancy_apply (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) (a : Fˣ) :
    (principalDiscrepancy A ι a : ℂ) =
      ((Classical.choose (exists_fractional_ideal_character A ι).exists)
        (ClassCharacterSteps.principalIdealMap A a) : ℂ) *
      (∏ w : InfinitePlace F,
        DHCubic.infinityComponent (DHCubic.E0 F A) F ι w
          (w.embedding (a : F)))⁻¹ := by
  simp only [principalDiscrepancy, MonoidHom.mul_apply, MonoidHom.comp_apply,
    MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, infinityDiagonalProduct_apply]

theorem principalDiscrepancy_primary_congruence (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) (α : 𝓞 F) (hα : α ≠ 0)
    (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)})
    (I : A.Exterior) (hI : I.val = Ideal.span {α})
    (a : Fˣ) (ha : (a : F) = (α : F)) :
    principalDiscrepancy A ι a = 1 := by
  let r : A.R := algebraMap (𝓞 F) A.R α
  have hr : A.Generates I r := by
    constructor
    · intro h
      apply hα
      apply (IsFractionRing.injective (𝓞 F) F)
      have h' := congrArg (fun x : A.R => (x : F)) h
      simpa [r] using h'
    · change Ideal.span {algebraMap (𝓞 F) A.R α} = Ideal.map _ I.val
      rw [hI, Ideal.map_span, Set.image_singleton]
  have har : (a : F) = (r : F) := by simpa [r] using ha
  have hp : ClassCharacterGluing.exteriorFractionalUnit A I =
      ClassCharacterSteps.principalIdealMap A a :=
    ClassCharacterGluing.exteriorFractionalUnit_generator A I a r hr har
  have hk := Classical.choose_spec (exists_fractional_ideal_character A ι).exists I
  rw [hp] at hk
  have hl := DHCubic.lambdaF_principal_congruence (DHCubic.E0 F A) F ι α hα hα3
  change DHCubic.lambda F A ι (Ideal.span {α}) = _ at hl
  rw [hI, hl] at hk
  apply Circle.ext
  rw [principalDiscrepancy_apply, hk, ha]
  have hn : (∏ w : InfinitePlace F,
      DHCubic.infinityComponent (DHCubic.E0 F A) F ι w (w.embedding (α : F))) ≠ 0 := by
    rw [← ha, ← infinityDiagonalProduct_apply A ι a]
    exact Circle.coe_ne_zero _
  simpa using mul_inv_cancel₀ hn

theorem principalDiscrepancy_primary_ratio (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ)
    (α β : 𝓞 F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)})
    (hβ3 : β - 1 ∈ Ideal.span {(3 : 𝓞 F)})
    (I J : A.Exterior) (hI : I.val = Ideal.span {α})
    (hJ : J.val = Ideal.span {β}) (a : Fˣ)
    (ha : (a : F) = (α : F) / (β : F)) :
    principalDiscrepancy A ι a = 1 := by
  have hα0 : (α : F) ≠ 0 := fun h => hα ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hβ0 : (β : F) ≠ 0 := fun h => hβ ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  let aα : Fˣ := Units.mk0 (α : F) hα0
  let aβ : Fˣ := Units.mk0 (β : F) hβ0
  have ha' : a = aα / aβ := by
    apply Units.ext
    simpa [aα, aβ, Units.val_div_eq_div_val] using ha
  rw [ha', map_div]
  rw [principalDiscrepancy_primary_congruence A ι α hα hα3 I hI aα rfl,
    principalDiscrepancy_primary_congruence A ι β hβ hβ3 J hJ aβ rfl]
  simp

theorem finite_normalization_of_open_conductor (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ)
    (K : OpenSubgroup ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ))
    (hK : ∀ a : Fˣ, (A.diagonal a).2 ∈ K → principalDiscrepancy A ι a = 1) :
    ∃ τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle,
      Continuous τ ∧ ∀ a : Fˣ,
        (τ ((A.diagonal a).2) : ℂ) =
          ((Classical.choose (exists_fractional_ideal_character A ι).exists)
            (ClassCharacterSteps.principalIdealMap A a) : ℂ) *
            (∏ w : InfinitePlace F,
              DHCubic.infinityComponent (DHCubic.E0 F A) F ι w
                (w.embedding (a : F)))⁻¹ := by
  obtain ⟨τ, hτ, hd⟩ := FiniteNormalizationTopology.extend_dense_character
    ((MonoidHom.snd _ _).comp A.diagonal)
    (FiniteNormalizationTopology.finite_diagonal_dense A) (principalDiscrepancy A ι) K hK
  refine ⟨τ, hτ, ?_⟩
  intro a
  exact (congrArg (fun z : Circle => (z : ℂ)) (hd a)).trans
    (principalDiscrepancy_apply A ι a)

theorem exists_finite_normalization (A : SArithmeticData F)
    (ι : DHCubic.E0 F A →+* ℂ) :
    let κ := Classical.choose (exists_fractional_ideal_character A ι).exists
    ∃ τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle,
      Continuous τ ∧ ∀ a : Fˣ,
        (τ ((A.diagonal a).2) : ℂ) =
          (κ (ClassCharacterSteps.principalIdealMap A a) : ℂ) *
            (∏ w : InfinitePlace F,
              DHCubic.infinityComponent (DHCubic.E0 F A) F ι w
                (w.embedding (a : F)))⁻¹ := by
  have h3 : (3 : 𝓞 F) ≠ 0 := by norm_num
  obtain ⟨K, hK⟩ := FiniteNormalization.exists_congruence_open_subgroup A.Sf 3 h3
  apply finite_normalization_of_open_conductor A ι K
  intro a ha
  have hS3 : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∈ v.asIdeal → v ∈ A.Sf := by
    intro v hv
    apply A.above_six v
    have h6 := v.asIdeal.mul_mem_left (2 : 𝓞 F) hv
    norm_num at h6 ⊢
    exact h6
  obtain ⟨α, β, hα, hβ, hα3, hβ3, hαS, hβS, hab⟩ :=
    FiniteNormalization.exists_primary_exterior_ratio A.Sf 3 h3 hS3 a (hK a ha)
  let I : A.Exterior := ⟨Ideal.span {α}, by
    simpa only [Ideal.span_singleton_eq_bot, ne_eq] using hα, hαS⟩
  let J : A.Exterior := ⟨Ideal.span {β}, by
    simpa only [Ideal.span_singleton_eq_bot, ne_eq] using hβ, hβS⟩
  exact principalDiscrepancy_primary_ratio A ι α β hα hβ hα3 hβ3 I J rfl rfl a hab

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.EisensteinExtensionArithmetic

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

namespace EisensteinInfinityRecipe

def angularCompletion (w : InfinitePlace F) : w.Completionˣ →* Circle :=
  Eisenstein.archimedeanAngular.comp
    (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom)

theorem continuous_angularCompletion (w : InfinitePlace F) :
    Continuous (angularCompletion w) := by
  exact Eisenstein.continuous_archimedeanAngular.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.units_map _)

def character (A : SArithmeticData F) (σ : F →+* ℂ) (w : InfinitePlace F) :
    w.Completionˣ →* Circle :=
  if w.embedding.comp (algebraMap (DHCubic.E0 F A) F) =
      σ.comp (algebraMap (DHCubic.E0 F A) F) then
    (angularCompletion w)⁻¹ else angularCompletion w

theorem character_apply (A : SArithmeticData F) (σ : F →+* ℂ)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    (character A σ w z : ℂ) =
      (DHCubic.infinityComponent (DHCubic.E0 F A) F
        (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
        (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹ := by
  have hz : InfinitePlace.Completion.extensionEmbedding w (z : w.Completion) ≠ 0 :=
    (map_ne_zero (InfinitePlace.Completion.extensionEmbedding w)).mpr z.ne_zero
  unfold character DHCubic.infinityComponent
  split_ifs
  · simp [angularCompletion, DHCubic.angular]
  · rw [DHCubic.star_angular _ hz, zpow_neg_one, inv_inv]
    rfl

theorem continuous_character (A : SArithmeticData F) (σ : F →+* ℂ)
    (w : InfinitePlace F) : Continuous (character A σ w) := by
  unfold character
  split_ifs
  · exact (continuous_angularCompletion w).inv
  · exact continuous_angularCompletion w

def product (A : SArithmeticData F) (σ : F →+* ℂ) : A.G →* Circle where
  toFun y := ∏ w : InfinitePlace F, character A σ w (y.1 w)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

theorem continuous_product (A : SArithmeticData F) (σ : F →+* ℂ) :
    Continuous (product A σ) := by
  apply continuous_finset_prod
  intro w _
  exact (continuous_character A σ w).comp ((continuous_apply w).comp continuous_fst)

theorem character_diagonal (A : SArithmeticData F) (σ : F →+* ℂ)
    (w : InfinitePlace F) (a : Fˣ) :
    (character A σ w ((A.diagonal a).1 w) : ℂ) =
      (DHCubic.infinityComponent (DHCubic.E0 F A) F
        (σ.comp (algebraMap (DHCubic.E0 F A) F)) w (w.embedding (a : F)))⁻¹ := by
  rw [character_apply]
  congr 2
  change InfinitePlace.Completion.extensionEmbedding w
    (algebraMap F w.Completion (a : F)) = _
  simp

end EisensteinInfinityRecipe

namespace EisensteinIdelicDescent

open scoped nonZeroDivisors

theorem continuous_glue (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (hχ : Continuous χ)
    (hprincipal : ∀ a : Fˣ,
      κ (ClassCharacterSteps.principalIdealMap A a) = χ (A.diagonal a)) :
    ∃ Φ : A.ArithmeticIdeleClasses →* Circle,
      Continuous Φ ∧ ∀ x : NumberField.IdeleGroup (𝓞 F) F,
        Φ (QuotientGroup.mk x) = ClassCharacterSteps.rawCharacter A χ κ x := by
  have hs (a : Fˣ) :
      ClassCharacterSteps.sRestriction A
        (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = A.diagonal a := by
    ext <;> rfl
  have hi (a : Fˣ) :
      ClassCharacterSteps.exteriorIdealMap A
        (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
          ClassCharacterSteps.principalIdealMap A a := by
    change Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom
      (_root_.IdeleGroup.fractionalIdeal (_root_.IdeleGroup.principalIdele F a)) = _
    rw [_root_.IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, coe_toPrincipalIdeal]
    change (FractionalIdeal.extendedHom F A.R)
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F)) =
        FractionalIdeal.spanSingleton A.R⁰ (a : F)
    rw [FractionalIdeal.extendedHom_spanSingleton (A := 𝓞 F) (K := F) F A.R]
    congr 1
    have hm : (IsFractionRing.map (K := F) (L := F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) A.R)) = RingHom.id F := by
      apply IsLocalization.ringHom_ext (𝓞 F)⁰
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply, IsFractionRing.map,
        IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply (𝓞 F) A.R F x).symm
    rw [hm]
    rfl
  have hker : NumberField.IdeleGroup.principalSubgroup (𝓞 F) F ≤
      (ClassCharacterSteps.rawCharacter A χ κ).ker := by
    rintro x ⟨a, rfl⟩
    change κ (ClassCharacterSteps.exteriorIdealMap A _) *
      (χ (ClassCharacterSteps.sRestriction A _))⁻¹ = 1
    rw [hi, hs, hprincipal]
    exact mul_inv_cancel _
  let Φ : A.ArithmeticIdeleClasses →* Circle :=
    QuotientGroup.lift _ (ClassCharacterSteps.rawCharacter A χ κ) hker
  have heval : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      Φ (QuotientGroup.mk x) = ClassCharacterSteps.rawCharacter A χ κ x :=
    fun _ => rfl
  exact ⟨Φ, ClassCharacterSteps.glued_character_continuous A χ κ Φ heval hχ, heval⟩

theorem glued_infinity (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (heval : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      Φ (QuotientGroup.mk x) = ClassCharacterSteps.rawCharacter A χ κ x)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    A.ideleInfiniteComponent Φ w z = (χ (Pi.mulSingle w z, 1))⁻¹ := by
  have h := (ClassCharacterSteps.glued_character_local_components A χ κ Φ heval).1
    (Pi.mulSingle w z, 1)
  simp only [Pi.mulSingle_apply, map_one, inv_one, Finset.prod_const_one,
    mul_one] at h
  have hp : (∏ x : InfinitePlace F,
      Φ (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F x (Pi.mulSingle (M := fun u : InfinitePlace F => u.Completionˣ) w z x))) =
        A.ideleInfiniteComponent Φ w z := by
    rw [Finset.prod_eq_single w]
    · simp [ideleInfiniteComponent]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, map_one, map_one]
    · simp
  simpa only [Finset.prod_inv_distrib, inv_inv, hp, Pi.one_apply, map_one,
    Finset.prod_const_one, inv_one, mul_one] using congrArg Inv.inv h

def sCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle) :
    A.G →* Circle :=
  (τ.comp (MonoidHom.snd _ _)) * (EisensteinInfinityRecipe.product A σ)⁻¹

theorem continuous_sCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle)
    (hτ : Continuous τ) : Continuous (sCharacter A σ τ) := by
  exact (hτ.comp continuous_snd).mul (EisensteinInfinityRecipe.continuous_product A σ).inv

theorem sCharacter_infinity (A : SArithmeticData F) (σ : F →+* ℂ)
    (τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    (sCharacter A σ τ (Pi.mulSingle w z, 1))⁻¹ =
      EisensteinInfinityRecipe.character A σ w z := by
  change (τ 1 * (∏ u : InfinitePlace F, EisensteinInfinityRecipe.character A σ u
    (Pi.mulSingle (M := fun u : InfinitePlace F => u.Completionˣ) w z u))⁻¹)⁻¹ = _
  rw [map_one, one_mul, inv_inv]
  rw [Finset.prod_eq_single w]
  · simp
  · intro u _ h
    rw [Pi.mulSingle_eq_of_ne h, map_one]
  · simp

theorem assemble (A : SArithmeticData F) (σ : F →+* ℂ)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (τ : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ) →* Circle)
    (hτ : Continuous τ)
    (hprincipal : ∀ a : Fˣ,
      τ ((A.diagonal a).2) = κ (ClassCharacterSteps.principalIdealMap A a) *
        EisensteinInfinityRecipe.product A σ (A.diagonal a))
    (hideal : ∀ I : A.Exterior,
      (κ (ClassCharacterGluing.exteriorFractionalUnit A I) : ℂ) =
        DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val) :
    ∃ Λ : A.ArithmeticIdeleClasses →* Circle,
      Continuous Λ ∧ A.IdeleCharacterUnramifiedOutside Λ ∧
      (∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
        A.RepresentsExteriorIdeal I x →
          (Λ (QuotientGroup.mk x) : ℂ) =
            DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val) ∧
      (∀ (w : InfinitePlace F) (z : w.Completionˣ),
        (A.ideleInfiniteComponent Λ w z : ℂ) =
          (DHCubic.infinityComponent (DHCubic.E0 F A) F
            (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
            (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹) := by
  have hp (a : Fˣ) : κ (ClassCharacterSteps.principalIdealMap A a) =
      sCharacter A σ τ (A.diagonal a) := by
    change _ = τ ((A.diagonal a).2) *
      (EisensteinInfinityRecipe.product A σ (A.diagonal a))⁻¹
    rw [hprincipal, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨Λ, hΛ, heval⟩ := continuous_glue A (sCharacter A σ τ) κ
    (continuous_sCharacter A σ τ hτ) hp
  refine ⟨Λ, hΛ,
    (ClassCharacterSteps.glued_character_local_components A (sCharacter A σ τ) κ Λ heval).2,
    ?_, ?_⟩
  · intro I x hx
    obtain ⟨hs, hi⟩ := ClassCharacterSteps.exterior_representative_maps A I x hx.1 hx.2.1 hx.2.2
    rw [heval]
    change ((κ (ClassCharacterSteps.exteriorIdealMap A x) *
      (sCharacter A σ τ (ClassCharacterSteps.sRestriction A x))⁻¹ : Circle) : ℂ) = _
    rw [hs, map_one, inv_one, mul_one, hi]
    exact hideal I
  · intro w z
    rw [glued_infinity A (sCharacter A σ τ) κ Λ heval, sCharacter_infinity]
    exact EisensteinInfinityRecipe.character_apply A σ w z

end EisensteinIdelicDescent

theorem eisensteinExtension (A : SArithmeticData F) (σ : F →+* ℂ) :
    ∃ Λ : A.ArithmeticIdeleClasses →* Circle,
      Continuous Λ ∧ A.IdeleCharacterUnramifiedOutside Λ ∧
      (∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
        A.RepresentsExteriorIdeal I x →
          (Λ (QuotientGroup.mk x) : ℂ) =
            DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val) ∧
      (∀ (w : InfinitePlace F) (z : w.Completionˣ),
        (A.ideleInfiniteComponent Λ w z : ℂ) =
          (DHCubic.infinityComponent (DHCubic.E0 F A) F
            (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
            (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹) := by
  let ι := σ.comp (algebraMap (DHCubic.E0 F A) F)
  let κ := Classical.choose
    (EisensteinExtensionArithmetic.exists_fractional_ideal_character A ι).exists
  have hideal : ∀ I : A.Exterior,
      (κ (ClassCharacterGluing.exteriorFractionalUnit A I) : ℂ) =
        DHCubic.lambda F A ι I.val :=
    Classical.choose_spec
      (EisensteinExtensionArithmetic.exists_fractional_ideal_character A ι).exists
  obtain ⟨τ, hτ, hprincipal⟩ :=
    EisensteinExtensionArithmetic.exists_finite_normalization A ι
  apply EisensteinIdelicDescent.assemble A σ κ τ hτ ?_ hideal
  intro a
  apply Circle.coe_injective
  rw [Circle.coe_mul, hprincipal]
  congr 1
  change _ = Circle.coeHom
    (∏ w : InfinitePlace F, EisensteinInfinityRecipe.character A σ w ((A.diagonal a).1 w))
  rw [map_prod]
  change (∏ w, DHCubic.infinityComponent (DHCubic.E0 F A) F ι w
    (w.embedding (a : F)))⁻¹ =
      ∏ w, (EisensteinInfinityRecipe.character A σ w ((A.diagonal a).1 w) : ℂ)
  simp_rw [EisensteinInfinityRecipe.character_diagonal]
  rw [Finset.prod_inv_distrib]

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection

end
