module

public import DedekindZetaZeroFree.Adeles.Quotients.AdditiveCompactness
public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceClassification

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPAdelicQuotient

open NumberField KPAdelicTopology KPAdelicDiagonal

variable (F : Type) [Field F] [NumberField F]

def rationalTraceQuotientCharacter (t : F) :
    AddChar (Adeles F ⧸ principalSubgroup F) Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (principalSubgroup F)
      ((adelicTraceCharacter F).mulShift
        (algebraMap F (Adeles F) t)).toAddMonoidHom (by
            intro a ha
            obtain ⟨r, rfl⟩ := ha
            change adelicTraceCharacter F (algebraMap F (Adeles F) t *
              algebraMap F (Adeles F) r) = 1
            rw [← map_mul, adelicTraceCharacter_diagonal]))

theorem rationalTraceQuotientCharacter_mk (t : F) (a : Adeles F) :
    rationalTraceQuotientCharacter F t (quotientMap F a) =
      adelicTraceCharacter F (algebraMap F (Adeles F) t * a) := by
  rfl

theorem continuous_rationalTraceQuotientCharacter (t : F) :
    Continuous (rationalTraceQuotientCharacter F t :
      (Adeles F ⧸ principalSubgroup F) → Circle) := by
  apply (QuotientAddGroup.isQuotientMap_mk (principalSubgroup F)).continuous_iff.mpr
  change Continuous (fun a : Adeles F =>
    adelicTraceCharacter F (algebraMap F (Adeles F) t * a))
  exact (continuous_adelicTraceCharacter F).comp (continuous_const.mul continuous_id)

end DedekindZetaZeroFree.KPAdelicQuotient

end

section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPAdelicQuotient

open NumberField KPAdelicTopology KPAdelicDiagonal

variable (F : Type) [Field F] [NumberField F]

private theorem arch_pairing (x y : InfiniteAdeleRing F) :
    adelicTraceCharacter F ((x * y, 0) : Adeles F) =
      Circle.exp (2 * Real.pi * KPArchTrace.infiniteTracePairing F x y) := by
  classical
  have hp : KPArchTrace.infiniteTracePairing F x y =
      ∑ w : InfinitePlace F, archTrace w (x w * y w) := by
    unfold KPArchTrace.infiniteTracePairing KPArchTrace.infiniteToSpace
    rw [PoissonArch.tracePairing]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply F y]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)
      (fun w => archTrace w (x w * y w))]
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      simp only [archTrace_of_isReal v.1 v.2, map_mul]
      rfl
    · rw [← Fintype.sum_equiv
        (Equiv.subtypeEquivRight (fun v => (InfinitePlace.not_isReal_iff_isComplex).symm))
        (fun v : {v : InfinitePlace F // v.IsComplex} => archTrace v.1 (x v.1 * y v.1))
        (fun v : {v : InfinitePlace F // ¬ v.IsReal} => archTrace v.1 (x v.1 * y v.1))
        (fun _ => rfl)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [archTrace_of_isComplex v.1 v.2, map_mul]
      rfl
  have hprod : ∀ (s : Finset (InfinitePlace F)) (f : InfinitePlace F → ℝ),
      Circle.exp (∑ w ∈ s, f w) = ∏ w ∈ s, Circle.exp (f w) := by
    intro s
    induction s using Finset.induction with
    | empty => intro f; simp
    | insert a s ha ih =>
        intro f
        rw [Finset.sum_insert ha, Finset.prod_insert ha, Circle.exp_add, ih]
  rw [hp, adelicTraceCharacter_apply, Finset.mul_sum, hprod]
  have hf : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      localFiniteCharacter F v ((0 : FiniteAdeles F) v)) = 1 := by
    change (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      localFiniteCharacter F v 0) = 1
    simp
  rw [hf, mul_one]
  rfl

private theorem frequency_unique (s t : F)
    (h : ∀ a : Adeles F, adelicTraceCharacter F (algebraMap F (Adeles F) s * a) =
      adelicTraceCharacter F (algebraMap F (Adeles F) t * a)) : s = t := by
  apply AdeleRing.algebraMap_injective (RingOfIntegers F) F
  apply sub_eq_zero.mp
  apply (adelicTraceCharacter_nondegenerate F _).mp
  intro a
  rw [sub_mul, (adelicTraceCharacter F).map_sub_eq_div]
  change adelicTraceCharacter F (algebraMap F (Adeles F) s * a) /
    adelicTraceCharacter F (algebraMap F (Adeles F) t * a) = 1
  rw [h, div_self']

theorem character_parametrization (χ : AddChar (Adeles F) Circle)
    (hχ : Continuous (χ : Adeles F → Circle))
    (hχF : ∀ r : F, χ (algebraMap F (Adeles F) r) = 1) :
    ∃! t : F, ∀ a : Adeles F,
      χ a = adelicTraceCharacter F (algebraMap F (Adeles F) t * a) := by
  classical
  obtain ⟨T, k, I, _, hker, hI, hIfiber, _, _⟩ :=
    kp_adelic_character_open_kernel F χ hχ
  let chiArch := χ.compAddMonoidHom (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeles F))
  have hchiArch : Continuous chiArch := hχ.comp (continuous_id.prodMk continuous_const)
  obtain ⟨y, hy, _⟩ := KPArchTrace.infinite_character_classification F chiArch hchiArch
  have hIχ : ∀ a : F, a ∈ (I : KPArchTrace.FractionalOIdeal F) →
      chiArch (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    have hfa : algebraMap F (FiniteAdeles F) a ∈
        KPAdelicCharacter.finiteIdealNeighborhood F T k := by
      change a ∈ (I : Set F) at ha
      rw [hIfiber] at ha
      exact ha
    have hh := hχF a
    have hsplit : algebraMap F (Adeles F) a =
        (algebraMap F (InfiniteAdeleRing F) a, 0) +
        (0, algebraMap F (FiniteAdeles F) a) := by
      apply Prod.ext <;> simp [Adeles, AdeleRing]
    rw [hsplit, χ.map_add_eq_mul, hker _ hfa, mul_one] at hh
    exact hh
  obtain ⟨t, _, ht⟩ := KPArchTrace.infinite_character_parameter_mem_inverseDifferent
    F I hI chiArch hchiArch y hy hIχ
  have harch : ∀ x : InfiniteAdeleRing F, χ (x, 0) =
      adelicTraceCharacter F (Mul.mul (α := Adeles F) (algebraMap F (Adeles F) t) (x, 0)) := by
    intro x
    have hh := hy x
    rw [← ht] at hh
    change χ (x, 0) = _ at hh
    rw [hh]
    have hm : Mul.mul (α := Adeles F) (algebraMap F (Adeles F) t) (x, 0) =
        (x * algebraMap F (InfiniteAdeleRing F) t, 0) := by
      apply Prod.ext
      · change algebraMap F (InfiniteAdeleRing F) t * x =
          x * algebraMap F (InfiniteAdeleRing F) t
        exact mul_comm _ _
      · change algebraMap F (FiniteAdeles F) t * 0 = 0
        exact mul_zero _
    rw [hm, arch_pairing]
  let ψ := (adelicTraceCharacter F).mulShift (algebraMap F (Adeles F) t)
  have hψ : Continuous ψ := (continuous_adelicTraceCharacter F).comp
    (continuous_const.mul continuous_id)
  have hψF : ∀ r : F, ψ (algebraMap F (Adeles F) r) = 1 := by
    intro r
    change adelicTraceCharacter F (algebraMap F (Adeles F) t *
      algebraMap F (Adeles F) r) = 1
    rw [← map_mul, adelicTraceCharacter_diagonal]
  have hfinite : ∀ b : FiniteAdeles F, χ (0, b) = ψ (0, b) := by
    have heq : (fun b : FiniteAdeles F => χ (0, b)) =
        (fun b : FiniteAdeles F => ψ (0, b)) := by
      apply (finiteAdeles_diagonal_denseRange F).equalizer
        (hχ.comp (continuous_const.prodMk continuous_id))
        (hψ.comp (continuous_const.prodMk continuous_id))
      funext r
      have hc := hχF r
      have hp := hψF r
      have hd : algebraMap F (Adeles F) r =
          (algebraMap F (InfiniteAdeleRing F) r, 0) +
          (0, algebraMap F (FiniteAdeles F) r) := by apply Prod.ext <;> simp [Adeles, AdeleRing]
      rw [hd, χ.map_add_eq_mul] at hc
      rw [hd, ψ.map_add_eq_mul] at hp
      have ha := harch (algebraMap F (InfiniteAdeleRing F) r)
      change χ (algebraMap F (InfiniteAdeleRing F) r, 0) =
        ψ (algebraMap F (InfiniteAdeleRing F) r, 0) at ha
      rw [ha] at hc
      exact mul_left_cancel (hc.trans hp.symm)
    exact fun b => congrFun heq b
  have hall : ∀ a : Adeles F, χ a = ψ a := by
    intro a
    have hd : a = (a.1, 0) + (0, a.2) := by apply Prod.ext <;> simp [Adeles, AdeleRing]
    conv_lhs => rw [hd, χ.map_add_eq_mul]
    conv_rhs => rw [hd, ψ.map_add_eq_mul]
    rw [hfinite, harch]
    rfl
  refine ⟨t, hall, ?_⟩
  intro s hs
  exact frequency_unique F s t (fun a => (hs a).symm.trans (hall a))

theorem quotient_character_parametrization
    (χ : AddChar (Adeles F ⧸ principalSubgroup F) Circle)
    (hχ : Continuous (χ : (Adeles F ⧸ principalSubgroup F) → Circle)) :
    ∃! t : F, χ = rationalTraceQuotientCharacter F t := by
  let χA := χ.compAddMonoidHom (quotientMap F)
  have hχA : Continuous χA := hχ.comp QuotientAddGroup.continuous_mk
  have hχAF : ∀ r : F, χA (algebraMap F (Adeles F) r) = 1 := by
    intro r
    change χ (quotientMap F (algebraMap F (Adeles F) r)) = 1
    have hz : quotientMap F (algebraMap F (Adeles F) r) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨r, rfl⟩
    rw [hz, χ.map_zero_eq_one]
  obtain ⟨t, ht, hu⟩ := character_parametrization F χA hχA hχAF
  refine ⟨t, ?_, ?_⟩
  · apply AddChar.ext
    intro q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (principalSubgroup F) q
    exact ht a
  · intro s hs
    apply hu s
    intro a
    change χ (quotientMap F a) = _
    rw [hs, rationalTraceQuotientCharacter_mk]

end DedekindZetaZeroFree.KPAdelicQuotient

end
end
