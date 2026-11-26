module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Comparing finite-place completion models

For an exact extension `w` of the normalized absolute value at a finite
place `v` of `K`, its centre `W` is a finite place of `L`.  The absolute
values `w` and the standard normalized absolute value at `W` differ by a
positive real power.  Consequently the identity on `L` extends to a ring
equivalence between their completions and preserves the valuation ring.

Composing with the existing comparison between the standard
absolute-value completion and mathlib's concrete adic completion gives the
local factor comparison used in the adelic restricted-product bridge.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- The standard absolute value at the centre of an exact extension has
the same valuation subring as that exact extension. -/
theorem finitePlaceExtension_adicAbv_valuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    absoluteValueValuationSubring
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩) =
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionValuationSubring_eq_localization,
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).valuationSubringAtPrime_eq_valuationSubring]
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x ≤ 1 ↔
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).valuation L x ≤ 1
  rw [HeightOneSpectrum.adicAbv_def]
  exact_mod_cast
    WithZeroMulInt.toNNReal_le_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w))

omit [FiniteDimensional K L] in
/-- The exact extension and the standard absolute value at its centre are
equivalent absolute values. -/
theorem finitePlaceExtension_isEquiv_adicAbv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.IsEquiv
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)) := by
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  have hle (y : L) :
      w.1 y ≤ 1 ↔
        HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w) y ≤ 1 := by
    rw [← mem_absoluteValueValuationSubring_iff
        w.1 (finitePlaceExtension_nonarchimedean
          (K := K) (L := L) v w),
      ← mem_absoluteValueValuationSubring_iff
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩)]
    change
      y ∈ finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w ↔
        y ∈ absoluteValueValuationSubring
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w))
          (finitePlaceExtension_nonarchimedean
            (K := L) (L := L)
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)
            ⟨HeightOneSpectrum.adicAbv L
                (finitePlaceExtensionCentre
                  (K := K) (L := L) v w),
              fun _ => rfl⟩)
    rw [finitePlaceExtension_adicAbv_valuationSubring]
  by_cases hx : x = 0
  · subst x
    simp
  calc
    w.1 x < 1 ↔ 1 < (w.1 x)⁻¹ :=
      (one_lt_inv₀ (w.1.pos hx)).symm
    _ ↔ 1 < w.1 x⁻¹ := by rw [map_inv₀]
    _ ↔ ¬ w.1 x⁻¹ ≤ 1 := not_le.symm
    _ ↔ ¬ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ ≤ 1 :=
      not_congr (hle x⁻¹)
    _ ↔ 1 < HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ := not_le
    _ ↔ 1 < (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x)⁻¹ := by
      rw [map_inv₀]
    _ ↔ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x < 1 :=
      one_lt_inv₀
        ((HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)).pos hx)

/-- The positive exponent relating an exact extension to the standard
absolute value at its centre. -/
noncomputable def finitePlaceExtensionExponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) : ℝ :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionExponent_pos
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    0 < finitePlaceExtensionExponent
      (K := K) (L := L) v w :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose_spec.1

omit [FiniteDimensional K L] in
theorem finitePlaceExtension_adicAbv_eq_rpow
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x =
      w.1 x ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w :=
  (congrFun
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w)).choose_spec.2 x).symm

/-- The identity on `L`, regarded as a ring equivalence between the two
normed copies determined by the equivalent absolute values. -/
noncomputable def finitePlaceExtensionWithAbsRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    WithAbs w.1 ≃+*
      WithAbs
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) :=
  WithAbs.congr w.1
    (HeightOneSpectrum.adicAbv L
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))
    (RingEquiv.refl L)

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w) :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w) |>.continuous

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_symm_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w).symm := by
  rw [finitePlaceExtensionWithAbsRingEquiv,
    WithAbs.congr_symm]
  exact
    ((AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w).symm).continuous

/-- The completion comparison induced by the identity on `L`. -/
noncomputable def finitePlaceExtensionCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)).Completion :=
  (AbsoluteValue.Completion.equiv _).trans
    ((UniformSpace.Completion.mapRingEquiv
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w)
      (finitePlaceExtensionWithAbsRingEquiv_continuous
        (K := K) (L := L) v w)
      (finitePlaceExtensionWithAbsRingEquiv_symm_continuous
        (K := K) (L := L) v w)).trans
      (AbsoluteValue.Completion.equiv _).symm)

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      AbsoluteValue.toCompletion
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) x := by
  rw [AbsoluteValue.toCompletion_apply, AbsoluteValue.toCompletion_apply,
    finitePlaceExtensionCompletionRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AbsoluteValue.Completion.equiv_apply, AbsoluteValue.Completion.toCompletion_coe,
    UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (uniformContinuous_addMonoidHom_of_continuous
        (finitePlaceExtensionWithAbsRingEquiv_continuous
          (K := K) (L := L) v w)),
    AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.ofCompletion_coe]
  rfl

omit [FiniteDimensional K L] in
/-- The completion comparison is continuous. -/
theorem finitePlaceExtensionCompletionRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w) := by
  have h :
      (finitePlaceExtensionCompletionRingEquiv (K := K) (L := L) v w :
          w.1.Completion → _) =
        AbsoluteValue.Completion.ofCompletion ∘
          UniformSpace.Completion.map
            (finitePlaceExtensionWithAbsRingEquiv (K := K) (L := L) v w) ∘
          AbsoluteValue.Completion.toCompletion := by
    funext x
    simp only [finitePlaceExtensionCompletionRingEquiv, RingEquiv.trans_apply,
      Function.comp_apply, AbsoluteValue.Completion.equiv_apply,
      AbsoluteValue.Completion.equiv_symm_apply,
      UniformSpace.Completion.mapRingEquiv_apply]
  rw [h]
  exact (AbsoluteValue.Completion.continuous_ofCompletion
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre (K := K) (L := L) v w))).comp
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.Completion.continuous_toCompletion w.1))

omit [FiniteDimensional K L] in
/-- The norm on the standard completion is the positive power of the
norm on the exact-extension completion. -/
theorem finitePlaceExtensionCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  refine AbsoluteValue.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp
        (finitePlaceExtensionCompletionRingEquiv_continuous
          (K := K) (L := L) v w))
      (continuous_norm.rpow_const
        (fun _ => Or.inr
          (finitePlaceExtensionExponent_pos
            (K := K) (L := L) v w).le))
  · intro a
    rw [finitePlaceExtensionCompletionRingEquiv, RingEquiv.trans_apply,
      RingEquiv.trans_apply,
      AbsoluteValue.Completion.equiv_apply, AbsoluteValue.Completion.toCompletion_coe,
      UniformSpace.Completion.mapRingEquiv_apply,
      UniformSpace.Completion.map_coe
        (uniformContinuous_addMonoidHom_of_continuous
          (finitePlaceExtensionWithAbsRingEquiv_continuous
            (K := K) (L := L) v w)),
      AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.ofCompletion_coe,
      AbsoluteValue.Completion.norm_coe,
      AbsoluteValue.Completion.norm_coe]
    exact finitePlaceExtension_adicAbv_eq_rpow
      (K := K) (L := L) v w (WithAbs.equiv w.1 a)

/-- The existing comparison from the standard absolute-value completion
to the concrete adic completion is an isometry. -/
theorem relativeFinitePlaceCompletionRingEquiv_norm
    (W : HeightOneSpectrum (𝓞 L))
    (x : (HeightOneSpectrum.adicAbv L W).Completion) :
    ‖relativeFinitePlaceCompletionRingEquiv W x‖ = ‖x‖ := by
  change ‖relativeFinitePlaceCompletionRingHom W x‖ = ‖x‖
  exact
    (relativeFinitePlaceCompletionRingHom_isometry W).norm_map_of_map_zero
      (map_zero (relativeFinitePlaceCompletionRingHom W)) x

/-- The local factor comparison from an exact-extension completion to
the concrete completion at its centre. -/
noncomputable def finitePlaceExtensionAdicCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).adicCompletion L :=
  (finitePlaceExtensionCompletionRingEquiv
    (K := K) (L := L) v w).trans
    (relativeFinitePlaceCompletionRingEquiv
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionAdicCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    relativeFinitePlaceCompletionRingEquiv_norm,
    finitePlaceExtensionCompletionRingEquiv_norm]

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      FinitePlace.embedding
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    finitePlaceExtensionCompletionRingEquiv_toCompletion]
  change
    relativeFinitePlaceCompletionRingHom
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)
        (AbsoluteValue.toCompletion
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)) x) = _
  rw [AbsoluteValue.toCompletion_apply, relativeFinitePlaceCompletionRingHom_coe]
  rfl

omit [FiniteDimensional K L] in
/-- The local factor comparison identifies the valuation ring in the
exact-extension completion with the concrete adic integers. -/
theorem finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w x ∈
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w).adicCompletionIntegers L ↔
      x ∈ absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  have hrpow :
      ‖x‖ ^ finitePlaceExtensionExponent
          (K := K) (L := L) v w ≤ 1 ↔
        ‖x‖ ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
        (finitePlaceExtensionExponent_pos
          (K := K) (L := L) v w)
  constructor
  · intro hx
    have hnorm :=
      norm_le_one_of_mem_adicCompletionIntegers
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) hx
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm] at hnorm
    exact hrpow.mp hnorm
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w)
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm]
    exact hrpow.mpr hx

end
